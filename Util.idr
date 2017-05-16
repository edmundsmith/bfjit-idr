module Util

import Data.Vect

%language UniquenessTypes
%access public export

followedBy : (a->b) -> (b->c) -> a -> c
followedBy = flip (.)

flipEq : a = b -> b = a 
flipEq prf = rewrite prf in Refl

succDistributive : (n:Nat) -> (m:Nat) -> (S m + S n) = (S (S (m+n)))
succDistributive n m = do
	let rightSum = S (m + n)
	let inner = plusSuccRightSucc m n
	eqSucc (m + S n) (S (m + n)) (flipEq inner)
	

data FinList : (n : Nat) -> (a : Type*) -> Type* where
	FinNil : FinList (S n) a
	FinCons : a -> FinList (S n) a -> FinList n a

data FinTape : (llen:Nat) -> (rlen:Nat) -> (elem:Type*) -> Type* where
	FinCursor : Vect llen elem ->
				elem ->
				Vect rlen elem ->
				FinTape llen rlen elem

tapeLeft : FinTape (S l) r elem -> FinTape l (S r) elem
tapeLeft (FinCursor (h::t) e r) = FinCursor t h (e::r)
tapeRight : FinTape l (S r) elem -> FinTape (S l) r elem
tapeRight (FinCursor l e (h::t)) = FinCursor (e::l) h t

data InfTape : (elem:Type*) -> Type* where
	InfCursor : Lazy (Stream elem) -> elem -> Lazy (Stream elem) -> InfTape elem

infTapeRight : InfTape a -> InfTape a
infTapeRight (InfCursor l c (r::t)) = InfCursor (c::l) r t
infTapeLeft : InfTape a -> InfTape a
infTapeLeft (InfCursor (l::t) c r) = InfCursor t l (c::r)

interface Cursor (c: Type* -> Type*) where
	cursor : c a -> a
	updateCursor : (a -> a) -> c a -> c a

Cursor (FinTape llen rlen) where
	cursor (FinCursor _ c _) = c
	updateCursor f (FinCursor l c r) = FinCursor l (f c) r

Cursor InfTape where
	cursor (InfCursor _ c _) = c
	updateCursor f (InfCursor l c r) = InfCursor l (f c) r