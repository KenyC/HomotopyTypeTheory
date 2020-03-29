module Monoid

import Equality
import Algebra


infixr 12 :+:
infixr 13 :.:
data RationalExpression : Type where
	Constant : String -> RationalExpression
	Star : RationalExpression -> RationalExpression
	(:+:) : RationalExpression -> RationalExpression -> RationalExpression
	(:.:) : RationalExpression -> RationalExpression -> RationalExpression


reorder : List a -> List Nat -> List a
reorder l indices = [index i l | i <- indices, i < (length l)]

infixr 11 |~
data (|~) : List RationalExpression -> List RationalExpression -> Type where
	-- Axioms
	Eq : [r] |~ [r]

	Reorder : (indices : List Nat) -> l1 |~ l2 -> (reorder l1 indices) |~ l2

	-- Union rules
	LeftUnion : (a::l1) |~ l2 -> ((b::l1'') |~ l2) -> (((a :+: b)::(l1 ++ l1'')) |~ l2)

	-- RightUnionR : ((a :+: b)::l1) |~ l2 -> (b::l1) |~ l2
	RightUnionL : l1 |~ (a :: l2) -> (l1 |~ ((a :+: b) :: l2))
	RightUnionR : l1 |~ (a :: l2) -> (l1 |~ ((b :+: a) :: l2))



	-- Product rules


commutativity : (l1 : RationalExpression) -> (l2 : RationalExpression) -> 
                [l1 :+: l2] |~ [l2 :+: l1]
commutativity l1 l2 = LeftUnion premisse2 premisse1
                      where
                      --
                      premisse1 : [l2] |~ [l2 :+: l1]
                      premisse1 = RightUnionL {a = l2} {b = l1} $ Eq {r = l2}
                      -- 
                      premisse2 : [l1] |~ [l2 :+: l1] 
                      premisse2 = RightUnionR {a = l1} {b = l2} $ Eq {r = l1}



