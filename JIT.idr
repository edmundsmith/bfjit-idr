module JIT

import Effects
import Effect.State
import Effect.File
import Effect.StdIO
import Effect.System
import Effect.Exception
import Data.Bits

import Assembler
import CFFI
import BF

import Debug.Trace

%include C "sys/mman.h"
%include C "stdlib.h"
%include C "stdio.h"

%access public export

infixl 1 .|.
(.|.) : %static {n:Nat} -> machineTy n -> machineTy n -> machineTy n
(.|.) = or'

infixl 2 .&.
(.&.) : %static {n:Nat} -> machineTy n -> machineTy n -> machineTy n
(.&.) = and'

data IOEff : Effect where
	PerformIO : IO () -> sig IOEff ()

Handler IOEff IO where
	handle ctx (PerformIO io) k = do io; k () ()

IOEFF : EFFECT
IOEFF = MkEff () IOEff

performIO : IO () -> Effects.SimpleEff.Eff () [IOEFF]
performIO io = call $ PerformIO io

PROT_EXEC : Bits32
PROT_EXEC = 0x4
PROT_WRITE : Bits32
PROT_WRITE = 0x2
PROT_READ : Bits32
PROT_READ = 0x1
PROT_NONE : Bits32
PROT_NONE = 0x0

MAP_SHARED : Bits32
MAP_SHARED = 0x01
MAP_PRIVATE : Bits32
MAP_PRIVATE = 0x02
MAP_ANONYMOUS : Bits32
MAP_ANONYMOUS = 0x20

mmap : Ptr -> Bits64 -> Bits32 -> Bits32 -> Bits32 -> Bits64 -> IO Ptr
mmap ptr len prot flags fd off = 
	foreign FFI_C "mmap" 
		(Ptr -> Bits64 -> Bits32 -> Bits32 -> Bits32 -> Bits64 -> IO Ptr)
		ptr len prot flags fd off

mmap_executable : Composite -> IO Ptr
mmap_executable t = mmap null
			(prim__zextInt_B64 $ sizeOf t)
			(the (machineTy 2) PROT_EXEC .|. PROT_WRITE .|. PROT_READ)
			(the (machineTy 2) MAP_PRIVATE .|. MAP_ANONYMOUS)
			(prim__zextInt_B32 (-1))
			0

munmap : Ptr -> Bits64 -> IO Int
munmap ptr len = foreign FFI_C "munmap" (Ptr -> Bits64 -> IO Int) ptr len

withMMap : Composite -> (CPtr -> IO a) -> IO a
withMMap t f = do
	m <- mmap_executable t
	r <- f m
	munmap m (prim__zextInt_B64 $ sizeOf t) 
	pure r

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

executeJit : List Bits8 -> IO ()
executeJit bits = do
	let lbits = toIntNat $ length bits + 1
	let arrTy = the Composite (ARRAY lbits (T I8))
	withMMap arrTy (setAndExecuteBits bits arrTy)

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


emain : Effects.SimpleEff.Eff () [SYSTEM, STDIO, FILE (), IOEFF]
emain = 
	case !getArgs of
		[] => Effect.StdIO.putStrLn "Impossible: empty arg list"
		(prog::args) => do
			efor_ {b=()} args $ \arg => do
				putStrLn $ "Running " ++ arg
				Result fileContents <- lift $ readFile arg
						| err => putStrLn ("Unexpected error with: " ++ arg)
				lift $ performIO $ (ARRAY 4000 I8) ~~> \tape => do
					let tapeLoc = bytesToB64 $ reverse $ b64ToBytes $ !(foreign FFI_C "labs" (Ptr -> IO Bits64) tape)
					putStrLn $ show tapeLoc
					let llir = parseLLIR fileContents

					let mir = elevateLLIR llir
					let mir = optIR @{fixLoops} $ optIR @{mergeImm} mir
					--let mir = optIR @{mergeImm}  $ optIR @{reorderFixedLoops} mir
					let mir = optIR @{removeNops} $ optIR @{mergeImm} $ optIR @{maddifyLoops} $ mir

					let readyMIRJit = emitterMIR tapeLoc mir

					putStrLn $ show mir
					putStrLn "---------"
									
					--putStrLn "\nMIR:"
					--for_ readyMIRJit (Prelude.Interactive.putStr . show)
					putStrLn "Jit prepared!"
					executeJit readyMIRJit

io_emain : IO ()
io_emain = run emain
