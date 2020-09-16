module FunctionExtensionality

import Equality

data Segment : Type where
  Beginning : Segment
  End       : Segment

-- Axioms for higher inductive type
Path : Beginning :=: End


using (a : Type)
  indSegment : (x : a) -> 
               (y : a) -> 
               (p : x :=: y) ->
               (f : (Segment -> a) ** (eq1 : (f(Beginning) :=: x) **
                                      (eq2 : (f(End)       :=: y) **
                                      fmap f Path :=: (eq1 :>: p :>: (rev eq2)))))


-- Proving simple function extensionality
function_ext : {f : a -> b} -> {g : a -> b} -> ((x : a) -> ((f x) :=: (g x))) -> (f :=: g) 
function_ext {a=a} {b=b} {f=f} {g=g} p = ?hole
                             where
                                contraction : (x : a) -> (h : (Segment -> b) ** (eq1 : (h(Beginning) :=: f(x)) **
                                                                                (eq2 : (h(End)       :=: g(x)) **
                                                                                fmap h Path :=: (eq1 :>: (p x) :>: (rev eq2)))))
                                contraction x = indSegment (f x) (g x) (p x)


                                swap : (a1 -> b1 -> c1) -> b1 -> a1 -> c1
                                swap f y x = f x y

                                homotopy_full : (homotopy : Segment -> a -> b ** (homotopy(Beginning) :=: f, homotopy(End) :=: g))
                                homotopy_full = (swap reverse_homotopy ** )
                                                where
                                                    reverse_homotopy : a -> Segment -> b
                                                    reverse_homotopy x = fst (contraction x)

                                                    

                                function_path : (homotopy Beginning) :=: (homotopy End)
                                function_path = fmap homotopy Path 