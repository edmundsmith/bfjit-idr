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

emain : Effects.SimpleEff.Eff () [SYSTEM, STDIO, FILE (), IOEFF]
emain = 
	case !getArgs of
		[] => Effect.StdIO.putStrLn "Impossible: empty arg list"
		(prog::args) => f args {-with Effects 
			for_ args $ the (String -> Eff () [STDIO, FILE ()]) $ 
				\arg => 
					Effect.StdIO.putStrLn $ "Running " ++ arg
					Result fileContents <- readFile arg
						| err => Effect.StdIO.putStrLn ("Unexpected: " ++ arg ++ (show err))
					(ARRAY 4000 I8) ~~> \tape => do
						let tapeLoc = !(foreign FFI_C "labs" (Ptr -> IO Bits64) tape)
						executeJit $ emitterLLIR tapeLoc $ parseLLIR fileContents-}
			
				{-Result fileContents <- readFile arg 
					| err => Effect.StdIO.putStrLn ("Unexpected: " ++ arg ++ (show err))
				(ARRAY 4000 I8) ~~> \tape => do
					let tapeLoc = !(foreign FFI_C "labs" (Ptr -> IO Bits64) tape)
					executeJit $ emitterLLIR tapeLoc $ parseLLIR bf-}
	--putStrLn ""
	where 
		f : List String -> Eff () [STDIO, SYSTEM, FILE (), IOEFF]
		f [] = pure ()
		f (arg::t) = do 
			Effect.StdIO.putStrLn $ "Running " ++ arg
			Result fileContents <- lift $ readFile arg
					| err => lift (Effect.StdIO.putStrLn ("Unexpected error with: " ++ arg))
			lift $ performIO $ (ARRAY 4000 I8) ~~> \tape => do
				putStrLn "Running on array"
				let tapeLoc = bytesToB64 $ reverse $ b64ToBytes $ !(foreign FFI_C "labs" (Ptr -> IO Bits64) tape)
				putStrLn $ show tapeLoc
				let llir = parseLLIR fileContents
				let mir = elevateLLIR llir
				--putStrLn $ show mir
				let mir = optIR @{fixLoops} $ optIR @{mergeImm} mir
				let readyJit = emitterLLIR tapeLoc llir
				putStrLn "\nLLIR:"
				for_ readyJit (Prelude.Interactive.putStr . show)
				let readyMIRJit = emitterMIR tapeLoc mir
				putStrLn "\nMIR:"
				for_ readyMIRJit (Prelude.Interactive.putStr . show)
				putStrLn "Jit prepared!"
				executeJit readyMIRJit
				--executeJit $ emitterLLIR tapeLoc $ parseLLIR fileContents
			f t

io_emain : IO ()
io_emain = run emain

jmain : IO ()
jmain = do
	let jit = runJit (factorial $ prim__zextInt_B64 $ prim__fromStrInt $ trim $ !getLine)
	putStrLn $ show jit
	case jit of
		Right comp => do 
			executeJit (mach comp)
			pure ()
		Left err => putStrLn err
	bf <- getLine
	(ARRAY 4000 I8) ~~> \tape => do
		let ptrRaw = !(foreign FFI_C "labs" (Ptr -> IO Bits64) tape)
		foreign FFI_C "printf" (String -> Ptr -> IO ()) "%p\n" tape
		--let ptrRaw = the Bits64 $ really_believe_me ptr
		putStrLn $ show ptrRaw
		let ptrRaw = bytesToB64 $ reverse $ b64ToBytes ptrRaw
		{-putStrLn $ show !(prim_peek64 ptr 0)
		putStrLn $ show !(prim_peek64 ptr 8)
		putStrLn $ show !(prim_peek64 ptr 16)
		putStrLn $ show !(prim_peek64 ptr 24)-}
		executeJit $ emitterLLIR ptrRaw $ parseLLIR $ bf
		putStr $ show !(prim_peek64 tape 0)
		putStr ","
		putStr $ show !(prim_peek64 tape 8)
		putStr ","
		putStr $ show !(prim_peek64 tape 16)
		putStr ","
		putStr $ show !(prim_peek64 tape 24)

	putStrLn "Done!"
