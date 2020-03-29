module Monoid

import Equality

%hide Semigroup
%hide Monoid

%access export

infixr 12 <>
interface Magma (a : Type) where
	(<>) : a -> a -> a


interface Magma a => Semigroup (a : Type) where
	associativity : (x : a) -> (y : a) -> (z : a) -> 
	                x <> (y <> z) :=: (x <> y) <> z


interface (Magma a, Semigroup a) => Monoid (a : Type) where
	neuter : a

	leftNeutrality : (x : a) -> 
	                 x :=: (x <> neuter)
	rightNeutrality : (x : a) -> 
	                 x :=: (neuter <> x)

