module JIT

import Effects
import Effect.State
import Effect.File
import Effect.StdIO
import Effect.Exception
import Data.Bits

import Assembler
import CFFI
import BF

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
	for_ [0 .. pred $ Prelude.List.length bits] $ \i => do
		bits8 <- case (index' i bits) of
			Just bits8 => pure bits8
			Nothing => putStrLn ("Out of index: " ++ show i) >>= \x => pure (the Bits8 0)
		poke I8 ((arr#i) ptr) bits8
		putStr $ show bits8
		pure ()
	putStr "\nWow! "
	putStrLn $ show !(run_int_int_ptr ptr 0)
	pure ()

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
	(ARRAY 4000 I8) ~~> \ptr => do
		let ptrRaw = !(foreign FFI_C "labs" (Ptr -> IO Bits64) ptr)
		foreign FFI_C "printf" (String -> Ptr -> IO ()) "%p\n" ptr
		--let ptrRaw = the Bits64 $ really_believe_me ptr
		putStrLn $ show ptrRaw
		let ptrRaw = bytesToB64 $ reverse $ b64ToBytes ptrRaw
		{-putStrLn $ show !(prim_peek64 ptr 0)
		putStrLn $ show !(prim_peek64 ptr 8)
		putStrLn $ show !(prim_peek64 ptr 16)
		putStrLn $ show !(prim_peek64 ptr 24)-}
		executeJit $ emitterLLIR ptrRaw $ parseLLIR $ bf
		putStr $ show !(prim_peek64 ptr 0)
		putStr ","
		putStr $ show !(prim_peek64 ptr 8)
		putStr ","
		putStr $ show !(prim_peek64 ptr 16)
		putStr ","
		putStr $ show !(prim_peek64 ptr 24)
	putStrLn "Done!"
