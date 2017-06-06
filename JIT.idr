module JIT

import Effects
import Effect.State
import Effect.File
import Effect.StdIO
import Effect.System
import Effect.Exception
--import Effect.Memory
import Data.Bits

import Assembler
import CFFI
import BF
import MMap
import Malloc

import Debug.Trace


%include C "stdlib.h"
%include C "stdio.h"

%access public export


data IOEff : Type -> Effect where
	PerformIO : IO a -> NoResourceEffect.sig (IOEff a) ()

Handler (IOEff a) IO where
	handle ctx (PerformIO io) k = do x <- io; k () ()

IOEFF : Type -> EFFECT
IOEFF a = MkEff () (IOEff a)

performIO : IO a -> Effects.SimpleEff.Eff () [IOEFF a]
performIO io = call $ PerformIO io



{-run_fptr : %static {fptr:Type} -> CPtr -> fptr
run_fptr {fptr} ptr = case fptr of 
	(b -> c) => the (b->c) $ \x:b => foreign FFI_C "%dynamic" (Ptr -> b -> c) ptr x
	(a -> b -> c) => \x => run_fptr {fptr=b->c} ptr -}
run_int_int_ptr : CPtr -> Int -> IO Int
run_int_int_ptr ptr = foreign FFI_C "%dynamic" (Ptr -> Int -> IO Int) ptr

setAndExecuteBits : List Bits8 -> Composite -> CPtr -> IO ()
setAndExecuteBits bits arr ptr = do
		putStrLn "Setting bytes"
		loopFrom' 0 bits ptr
		putStrLn "\nWow!"
		putStrLn $ show !(run_int_int_ptr ptr 0)
		pure ()

	where
	loopFrom' : Int -> List Bits8 -> CPtr -> IO ()
	loopFrom' n (h::t) (CPt p o) = do
		poke I8 (CPt p (o + (sizeOf (fieldType arr Z) * n))) h
		loopFrom' (n+1) t (CPt p o)
	loopFrom' n [] ptr = pure ()

executeJit : List Bits8 -> Eff () [MMAP, IOEFF ()]
executeJit bits = do
	let lbits = toIntNat $ S $ length bits
	let arrTy = the Composite (ARRAY lbits (T I8))
	let ptrLen = prim__zextInt_B64 $ sizeOf arrTy
	--withMMap arrTy (setAndExecuteBits bits arrTy)
	let ptr = !(mmap_exe arrTy)
	let res = !(lift $ performIO $ setAndExecuteBits bits arrTy ptr)
	let ig = !(munmap ptr ptrLen)
	pure ()

factorial : Bits64 -> X86 ()
factorial n = do
	mov rcx (I n)
	mov rax (I 1)
	loop <- label
	mul rcx
	dec rcx
	cmp rcx (I 0)
	jnz loop
	ret

efor_ : List a -> (a -> Eff b effList) -> Eff () effList
efor_ (h::t) f = (f h) >>= \_ => (efor_ t f)
efor_ [] _ = pure ()

parseOpts : List String -> (List String, List String)
parseOpts l = parseOpts' (map unpack l) ([],[]) where
	parseOpts' : List (List Char) -> (List String, List String) -> (List String, List String)
	parseOpts' (with List ('-'::'-'::h)::t) (l,r) = parseOpts' t ((pack h)::l,r)
	parseOpts' (h::t) (l,r) = parseOpts' t (l, (pack h)::r)
	parseOpts' [] res = res

emain : Effects.SimpleEff.Eff () [SYSTEM, STDIO, FILE (), MMAP, MALLOC (), IOEFF ()]
emain = 
	case !getArgs of
		[] => putStrLn "Impossible: empty arg list"
		(prog::args) => do
			let (opts, files) = parseOpts args
			let irOpt = optPassMIRFor opts
			putStrLn $ "Opts: " ++ show opts
			efor_ {b=()} files $ \file => with Effect.StdIO with Effect.File do --'
				putStrLn $ "Running " ++ file
				case !(readFile file) of 
					Result fileContents => do
						putStrLn "Read:"
						putStrLn fileContents

						tapePtr <- calloc 4000
						
						let tapeLoc = bytesToB64 $ reverse $ b64ToBytes (unsafePerformIO $ (foreign FFI_C "labs" (Ptr -> IO Bits64) tapePtr))

						let llir = parseLLIR fileContents

						let mir = elevateLLIR llir

						{-let mir = optIR @{fixLoops} $ optIR @{mergeImm} mir
						let mir = optIR @{reorderFixedLoops} mir
						let mir = optIR @{removeNops} $ optIR @{mergeImm} $ optIR @{maddifyLoops} $ mir
						-}

						let mir = (optPassMIRFor opts mir)

						let readyJit = emitterMIR tapeLoc mir
						let jitLen = toIntNat $ length readyJit

						jitBuf <- mmap_exe (ARRAY jitLen I8)

						--putStrLn "Writing bytes"
						efor_ {b=()} (zip (the (List Int) [0..jitLen]) readyJit) $ \(off, byte) => 
							lift $ performIO $ poke I8 (CPt jitBuf off) byte

						

						--putStrLn $ show mir
						--putStrLn "---------"
										
						--putStrLn "\nMIR:"
						--for_ readyMIRJit (Prelude.Interactive.putStr . show)
						--putStrLn "Jit prepared!"
						performIO $ do _ <- run_int_int_ptr jitBuf 0; pure ()

						_ <- munmap jitBuf (prim__zextInt_B64 jitLen)
						free tapePtr

					err => putStrLn ("Unexpected error with: " ++ file)

io_emain : IO ()
io_emain = run emain
