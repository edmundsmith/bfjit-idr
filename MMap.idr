module MMap

import Effects
import Effect.State
import Data.Bits
import CFFI

%include C "sys/mman.h" 

%access public export
--mutual

data MMapFlag = ProtExec 
	| ProtWrite 
	| ProtRead
	| ProtNone 
	| MapShared
	| MapPrivate 
	| MapAnonymous

record MMapFlags where
	constructor MkMMapFlags
	prot, maps : Bits32

data MMap : Effect where
	CallMMap : Ptr -> Bits64 -> MMapFlags -> Bits32 -> Bits64 -> sig MMap Ptr
	CallUnMMap : Ptr -> Bits64 -> sig MMap Int

MMAP : EFFECT
MMAP = MkEff () MMap


addFlag : MMapFlag -> MMapFlags -> MMapFlags
addFlag ProtExec x =  record { prot $= (or' {n=2} 0x4)} x
addFlag ProtWrite x = record { prot $= (or' {n=2} 0x2)} x
addFlag ProtRead x =  record { prot $= (or' {n=2} 0x1)} x
addFlag ProtNone x =  record { maps $= (or' {n=2} 0x0)} x
addFlag MapShared x =    record { maps $= (or' {n=2} 0x1)} x
addFlag MapPrivate x =   record { maps $= (or' {n=2} 0x2)} x
addFlag MapAnonymous x = record { maps $= (or' {n=2} 0x20)} x

flags : Foldable f => f MMapFlag -> MMapFlags
flags l = foldr addFlag (MkMMapFlags 0 0) l

PROT_EXEC : MMapFlag
PROT_EXEC = ProtExec
PROT_WRITE : MMapFlag
PROT_WRITE = ProtWrite
PROT_READ : MMapFlag
PROT_READ = ProtRead
PROT_NONE : MMapFlag
PROT_NONE = ProtNone

MAP_SHARED : MMapFlag
MAP_SHARED = MapShared
MAP_PRIVATE : MMapFlag
MAP_PRIVATE = MapPrivate
MAP_ANONYMOUS : MMapFlag
MAP_ANONYMOUS = MapAnonymous

concatXElem : Elem e (e::es) -> (l: List a) -> Elem e (l++(e::es))
concatXElem prf [] = Here
concatXElem prf (h::t) = There (concatXElem prf t)

--concatElemY : (l : List a) -> {auto ok : NonEmpty l} -> Elem (head {ok} l) l
--concatElemY l = with List the (Elem (head l) l) Here

{-mmap : (ptr:Ptr) -> (len:Bits64) -> (flags:MMapFlags)-> (fd:Bits32) -> (off:Bits64) ->
	EffM m Ptr (x ++ [MMAP] ++ y)
		(\v => updateResTy v (x ++ MMAP :: y) (concatXElem Here x) (CallMMap ptr len flags fd off))
mmap ptr len flags fd off {x} =
	let prf = concatXElem Here x in call (CallMMap ptr len flags fd off) {prf}

munmap : (ptr:Ptr) -> (len:Bits64) ->
	EffM m Int (x ++ [MMAP] ++ y)
		(\v => updateResTy v (x ++ MMAP :: y) (concatXElem Here x) (CallUnMMap ptr len))
munmap ptr len {x} = let prf = concatXElem Here x in call (CallUnMMap ptr len) {prf}

mmap_exe : {x:List EFFECT} -> (t:Composite) -> EffM m Ptr (x ++ [MMAP] ++ y)
	(\v => updateResTy v
            (x ++ MMAP :: y)
            (concatXElem Here x)
            (CallMMap Prelude.Strings.null
                      (prim__zextInt_B64 (sizeOf t))
                      (flags [PROT_EXEC, PROT_WRITE, PROT_READ, MAP_PRIVATE, MAP_ANONYMOUS])
                      (prim__zextInt_B32 (-1))
                      0))
mmap_exe t {x} {y} = 
	(mmap null
			(prim__zextInt_B64 $ sizeOf t)
			(with List flags [PROT_EXEC, PROT_WRITE, PROT_READ, MAP_PRIVATE, MAP_ANONYMOUS])
			(prim__zextInt_B32 (-1))
			0)-}
namespace Eff
	mmap : (ptr:Ptr) -> (len:Bits64) -> (flags:MMapFlags)-> (fd:Bits32) -> (off:Bits64) ->
		Eff Ptr [MMAP]
	mmap ptr len flags fd off = call (CallMMap ptr len flags fd off)

	munmap : (ptr:Ptr) -> (len:Bits64) -> Eff Int [MMAP]
	munmap ptr len = call (CallUnMMap ptr len)

	mmap_exe : (t:Composite) -> Eff Ptr [MMAP]
	mmap_exe t = mmap null
			(prim__zextInt_B64 $ sizeOf t)
			(with List flags [PROT_EXEC, PROT_WRITE, PROT_READ, MAP_PRIVATE, MAP_ANONYMOUS])
			(prim__zextInt_B32 (-1))
			0

withMMap : (ty:Composite) -> 
	{auto eli:SubElem MMAP effi} ->
	{auto elo:SubElem MMAP effo} ->
	{auto seli:SubList [MMAP] effi} ->
	{auto selo:SubList [MMAP] effo} ->
	{auto selel: SubList effi effo} ->
	{auto updateInvariant1 : (updateWith [MMAP] effo selo) = effo} -> 
	{auto updateInvariant2 : (updateWith effi effo selel) = effo} -> 
	(f:Ptr -> Eff a effi) -> Eff a effo
withMMap ty f {effo} {a} {updateInvariant1} {updateInvariant2} = ?hmm


infixl 1 .|.
private
(.|.) : %static {n:Nat} -> machineTy n -> machineTy n -> machineTy n
(.|.) = or'


infixl 2 .&.
private
(.&.) : %static {n:Nat} -> machineTy n -> machineTy n -> machineTy n
(.&.) = and'



namespace IO
	
	public export
	mmap : Ptr -> Bits64 -> MMapFlags -> Bits32 -> Bits64 -> IO Ptr
	mmap ptr len flags fd off = 
		foreign FFI_C "mmap" 
			(Ptr -> Bits64 -> Bits32 -> Bits32 -> Bits32 -> Bits64 -> IO Ptr)
			ptr len (prot flags) (maps flags) fd off
	
	public export
	mmap_exe : Composite -> IO Ptr
	mmap_exe t = mmap null
			(prim__zextInt_B64 $ sizeOf t)
			(flags [PROT_EXEC, PROT_WRITE, PROT_READ, MAP_PRIVATE, MAP_ANONYMOUS])
			(prim__zextInt_B32 (-1))
			0
	
	public export
	munmap : Ptr -> Bits64 -> IO Int
	munmap ptr len = foreign FFI_C "munmap" (Ptr -> Bits64 -> IO Int) ptr len
	
	public export
	withMMap : Composite -> (CPtr -> IO a) -> IO a
	withMMap t f = do
		m <- mmap_exe t
		r <- f m
		munmap m (prim__zextInt_B64 $ sizeOf t) 
		pure r

Handler MMap IO where
	handle ctx (CallMMap ptr len flags fd off) k = do 
		ptr <- IO.mmap ptr len flags fd off
		k ptr ctx
	handle ctx (CallUnMMap ptr len) k = do 
		res <- IO.munmap ptr len
		k res ctx