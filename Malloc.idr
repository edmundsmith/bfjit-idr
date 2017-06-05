module Malloc

import Effects
import Effect.State
import Data.Bits
import CFFI

%include C "stdlib.h"

%access public export

data Initialised = Init | Uninit


data Malloc : Effect where
	Alloc : Int -> Initialised -> sig Malloc Ptr () Ptr
	Free : Ptr -> sig Malloc () Ptr ()

MALLOC : Type -> EFFECT
MALLOC t = MkEff t Malloc

Handler Malloc IO where
	handle ctx (Alloc len Init) k = do 
		ptr <- foreign FFI_C "calloc" (Bits64 -> Bits64 -> IO Ptr) (prim__zextInt_B64 len) 1
		k ptr ptr
	handle ctx (Alloc len Uninit) k = do 
		ptr <- foreign FFI_C "malloc" (Bits64 -> IO Ptr) (prim__zextInt_B64 len)
		k ptr ptr
	handle ctx (Free ptr) k = do 
		res <- foreign FFI_C "free" (Ptr -> IO ()) ptr
		k res ()

malloc : Int -> { [MALLOC ()] ==> [MALLOC Ptr] } Eff Ptr
malloc size = call $ Alloc size Uninit

calloc : Int -> { [MALLOC ()] ==> [MALLOC Ptr] } Eff Ptr
calloc size = call $ Alloc size Init

free : Ptr -> { [MALLOC Ptr] ==> [MALLOC ()] } Eff ()
free ptr = call $ Free ptr