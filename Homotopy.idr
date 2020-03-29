module Homotopy

import Equality

%access public export

infixr 10 ~.~
(~.~) : {p : a -> Type} -> (f : (x : a) -> p x) -> (g : (x : a) -> p x) -> Type
(~.~) {a=a} f g  = (x: a) -> (f x) :=: (g x)

infixr 10 ~~
(~~) : (f : a -> b) -> (g : a -> b) -> Type
(~~) {a=a} {b=b} f g = (~.~) {p = cst} f g
		where 
		cst : a -> Type
		cst x0 = b 



-- Homotopy is reflexive
reflexivity : {p : a -> Type} -> (f : (x: a) -> p x) -> f ~.~ f
reflexivity f x = Reflexive $ f x

-- Homotopy is symmetric
symmetry : {p : a -> Type} -> 
           (f : (x: a) -> p x) -> (g : (x: a) -> p x) ->
           f ~.~ g -> g ~.~ f
symmetry f g direct x = rev $ direct x

-- Homotopy is transitive
transitivity : {p : a -> Type} -> 
               (f : (x: a) -> p x) -> (g : (x: a) -> p x) -> (h : (x: a) -> p x) ->
               f ~.~ g -> g ~.~ h -> f ~.~ h
transitivity f g h eq1 eq2 x = (eq1 x) :>: (eq2 x)


-- Homotopy preserves composition
compose : {f1 : a -> b} -> {f2 : b -> c} -> {g1 : a -> b} -> {g2 : b -> c} ->
          (f1 ~~ g1) -> (f2 ~~ g2) -> ((f2 . f1) ~~ (g2 . g1))
-- f2 (f1 x) = f2 (g1 x) = g2 (g1 x)
compose {a=a} {f1=f1} {g1=g1} {f2=f2} {g2=g2} p1 p2 = \x : a => fmap f2 (p1 x) :>: p2 (g1 x)


-- Homotopy is natural transformation: the following diagram commutes

		-- f(x) --- fmap f p --- f(y)
		--  |                      |
		--  |                      |
		-- Homotopy(x)     Homotopy(y)
		--  |                      |
		--  |                      |
		-- g(x) --- fmap g p --- g(y)

-- Dependent function makes it hard to state
-- nat_transform : {x : a} -> {y : a} -> 
--                 {f : a -> b} -> {g : a -> b} -> 
--                 (H : f ~~ g) -> (p : x :=: y) ->
--                 ((H x) :>: (fmap g p)) :=: ((fmap f p) :>: (H y))


