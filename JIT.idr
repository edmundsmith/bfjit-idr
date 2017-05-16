module JIT

import Effects
import Effect.State
import Effect.File
import Effect.StdIO
import Effect.Exception

import Assembler
import CFFI

%include c "run.h"
%link c "run.o"

%access public export

PROT_EXEC : IO Int
PROT_EXEC = pure $ prim__truncB32_Int !(peek I32 !(foreign FFI_C "&idr_PROT_EXEC" (IO Ptr)))
PROT_READ : IO Int
PROT_READ = pure $ prim__truncB32_Int !(peek I32 !(foreign FFI_C "&idr_PROT_READ" (IO Ptr)))
PROT_WRITE : IO Int
PROT_WRITE = pure $ prim__truncB32_Int !(peek I32 !(foreign FFI_C "&idr_PROT_WRITE" (IO Ptr)))
PROT_NONE : IO Int
PROT_NONE = pure $ prim__truncB32_Int !(peek I32 !(foreign FFI_C "&idr_PROT_NONE" (IO Ptr)))

MAP_SHARED : IO Int
MAP_SHARED = pure $ prim__truncB32_Int !(peek I32 !(foreign FFI_C "&idr_MAP_SHARED" (IO Ptr)))
MAP_PRIVATE : IO Int
MAP_PRIVATE = pure $ prim__truncB32_Int !(peek I32 !(foreign FFI_C "&idr_MAP_PRIVATE" (IO Ptr)))
MAP_ANONYMOUS : IO Int
MAP_ANONYMOUS = pure $ prim__truncB32_Int !(peek I32 !(foreign FFI_C "&idr_MAP_ANONYMOUS" (IO Ptr)))

mmap : Ptr -> Bits64 -> Int -> Int -> Int -> Bits64 -> IO Ptr
mmap ptr len prot flags fd off = 
	foreign FFI_C "run_mmap" 
		(Ptr -> Bits64 -> Int -> Int -> Int -> Bits64 -> IO Ptr)
		ptr len prot flags fd off

mmap_executable : Composite -> IO Ptr
mmap_executable t = do
	putStrLn $ (show !PROT_EXEC) ++ "," ++ (show !PROT_WRITE) ++ "," ++ (show !PROT_READ)
	r <- (mmap null
			(prim__zextInt_B64 $ sizeOf t)
			((!PROT_EXEC `prim__orInt` !PROT_WRITE) `prim__orInt` !PROT_READ) 
			(!MAP_PRIVATE `prim__orInt` !MAP_ANONYMOUS)
			(-1)
			0)
	putStrLn $ show (r == null)
	pure r
munmap : Ptr -> Bits64 -> IO Int
munmap ptr len = foreign FFI_C "run_munmap" (Ptr -> Bits64 -> IO Int) ptr len

withMMap : Composite -> (CPtr -> IO a) -> IO a
withMMap t f = do
	m <- mmap_executable t
	r <- f m
	munmap m (prim__zextInt_B64 $ sizeOf t) 
	pure r

external_runner : CPtr -> IO Int
external_runner ptr = foreign FFI_C "run" (Ptr -> IO Int) ptr

external_runner_internal : CPtr -> IO Int
external_runner_internal ptr = foreign FFI_C "%dynamic" (Ptr -> Int -> IO Int) ptr 0

make_exe : CPtr -> IO Int
make_exe ptr = foreign FFI_C "make_exe" (Ptr -> IO Int) ptr

diver : CPtr -> IO Int
diver arr = do
	--x <- foreign FFI_C "%dynamic" (Ptr -> Int -> IO Int) arr 0
	x <- external_runner_internal arr
	putStrLn $ "Wow " ++ show x
	pure x

magic_inner : List Bits8 -> Composite -> CPtr -> IO () -> Int -> IO ()
magic_inner bits comp cptr io off = io >>= \x => do
	bits8 <- case (index' (toNat off) bits) of 
		Just bits8 => pure bits8
		Nothing => putStrLn "Out of index" >>= \x => (pure (the Bits8 0))
	poke I8 (field comp (toNat off) cptr) bits8
	putStr $ show bits8
	pure ()

marker : CPtr -> IO ()
marker cptr = putStrLn "Cptr found"

magic : List Bits8 -> Composite -> CPtr -> IO ()
magic bits arr ptr = do
	putStrLn $ show $ toIntNat $ length bits
	foldl (magic_inner bits arr ptr) (pure ()) (enumFromTo 0 (toIntNat $ pred $ Prelude.List.length bits))
	putStrLn ""
	--let tr = the (CPtr -> List Bits8) (map (peek I8))
	--putStrLn $ foldl (\x => \y => x ++ show y) "" (tr ptr)
	--marker arr
	putStrLn $ show ! (make_exe ptr)
	diver ptr
	pure ()

executeJit : List Bits8 -> IO ()
executeJit bits = do
	let lbits = toIntNat $ length bits + 1
	let arrTy = the Composite (ARRAY lbits (T I8))
	withMMap arrTy (magic bits arrTy)

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
	let jit = runJit (factorial 10)
	putStrLn $ show jit
	case jit of
		Right comp => do 
			executeJit (mach comp)
			pure ()
		Left err => putStrLn err
