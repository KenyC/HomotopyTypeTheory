module TypeEquivalence

import Homotopy
import Equality

%access export

qinv : {a : Type} -> {b : Type} -> 
       (f : a -> b) -> Type
qinv {a=a} {b=b} f = (g : (b -> a) ** ((f . g) ~~ id, (g . f) ~~ id))


id_invertible : {a : Type} ->
                qinv (id {a=a})
id_invertible {a=a} = (id {a=a} ** (h1, h2))
                where
                h1 : (x : a) -> ((id {a=a} x) :=: x)
                h1 x = Reflexive x
                --
                h2 : (x : a) -> ((id {a=a} x) :=: x)
                h2 x = Reflexive x

composition_invertible :  {x: Type} -> {y: Type} -> {z : Type} ->
                          (p : x :=: y) ->
                          qinv ((:>:) {z=z} p)

-- (:>: p) : (y :=: z) -> (x :=: z)
composition_invertible {x=x} {y=y} {z=z} p = (inv ** (h1, h2))
                                               where 
                                                 inv : (x :=: z)  -> (y :=: z)
                                                 inv = (:>:) {z=z} (rev p)
                                                 --
                                                 h1 : (q : x :=: z) -> (((:>:) {z=z} p) (inv q) :=: q) -- This requires higher-order equalities
                                                 h2 : (r : y :=: z) -> ((inv $ (:>:) {z=z} p r) :=: r) 
                                                 -- 


isequiv : {a : Type} -> {b : Type} -> 
          (f : a -> b) ->
          Type
isequiv {a=a} {b=b} f = (g : (b -> a) ** (h : (b -> a) ** ((f . g) ~~ id, (h . f) ~~ id)))

transitivity_equiv : {f : a -> b} -> {g : b -> c} -> 
                     isequiv f -> isequiv g -> isequiv (g . f)
transitivity_equiv {a=a} {b=b} {c=c} {f=f} {g=g} (f_inv_r ** (f_inv_l ** (hr, hl))) 
                                                 (g_inv_r ** (g_inv_l ** (hr'', hl''))) = (f_inv_r . g_inv_r ** (f_inv_l . g_inv_l ** (hr1, hl1)))
                                                                           where
                                                                              hl1 : (f_inv_l . g_inv_l . g . f) ~~ id {a=a}
                                                                              hl1 = \x : a => fmap f_inv_l (hl'' $ f x) :>: (hl x)
                                                                              --
                                                                              hr1 : (g . f . f_inv_r . g_inv_r) ~~ id {a=c}
                                                                              hr1 = \x : c => fmap g (hr $ g_inv_r x) :>: (hr'' x)
                                                                              --
                                                                              -- hole1 : id ~~ id {a=b}
                                                                              -- auxl1 : id ~~ id {a=b}
                                                                              -- auxl1 = compose hole1 hole1 -- can't figure out the problem
                                                                              -- hl1 = (((reflexivity f_inv_l) `compose` hl'') `compose` (reflexivity f)) `transitivity` ?hole
                                                                           	  -- g-1 . g ~~ id  and f_inv_l ~~ f_inv_l and f ~~ f
                                                                           	  -- => f_inv_l . g_inv_l . g . f ~~ f_inv_l . f ~~ id 


-- Three essential properties of "isequiv"

-- A quasi-inverse is both a left and a right inverse
qinv_to_isequiv : {f : a -> b} ->
                  qinv f -> isequiv f
qinv_to_isequiv (g ** (h1, h2)) = (g ** (g ** (h1, h2))) 

-- If "isequiv" is true of f, then f has quasi-inverses
-- if h is a left inverse, and g a right inverse
-- the magic of combinatorics make hfg a left and right inverse
isequiv_to_qinv : {a : Type} -> {b : Type} ->
                  {f : a -> b} ->
                  isequiv f -> qinv f
isequiv_to_qinv {a=a} {b=b} {f=f} (g ** (h ** (h1, h2))) = (h . f . g ** (h1'', h2''))
                                            where
                                            h1'' : (x : b) -> (f (h (f (g x)))) :=: x 
                                            h1'' x = fmap f (h2 $ g x) :>: (h1 x)
                                            h2'' : (x : a) -> (h (f (g (f x)))) :=: x 
                                            h2'' x = fmap h (h1 $ f x) :>: (h2 x)

-- -- id is an equivalence
id_equivalence : {a : Type} -> isequiv (id {a=a})
id_equivalence = qinv_to_isequiv (id_invertible) 




-- -- All inhabitants of isequiv(f) are equal
all_inhabitant_equal : (p : isequiv f) -> (q : isequiv f) -> p :=: q
-- to implement: not sure how to prove this?

-- -- type equivalence
infix 10 :~: 
(:~:) : Type -> Type -> Type 
(:~:) a b = (f : (a -> b) ** isequiv f)

qinv_to_equiv : (f : a -> b) -> (qinv f) -> a :~: b
qinv_to_equiv f qinv_f = (f ** qinv_to_isequiv qinv_f)

-- -- destructors of identity types
pair_id_destructor : {x1 : a} -> {y1 : b} -> {x2 : a} -> {y2 : b} -> 
                     ((x1, y1) :=: (x2, y2)) :~: (x1 :=: x2, y1 :=: y2)
pair_id_destructor {a=a} {b=b} {x1=x1} {y1=y1} {x2=x2} {y2=y2} = qinv_to_equiv unpair (pair ** (h1, h2))
                                                     where
                                                        unpair : ((x1, y1) :=: (x2, y2)) -> (x1 :=: x2, y1 :=: y2)
                                                        unpair = uncons_pair_equ x1 y1 x2 y2
                                                        pair : (x1 :=: x2, y1 :=: y2) -> ((x1, y1) :=: (x2, y2)) 
                                                        pair = \(p1, p2) => cons_pair_equ x1 y1 x2 y2 p1 p2
                                                        -- This will be unbearably painful to write
                                                        h1 : (unpair . pair) ~~ id {a=(x1 :=: x2, y1 :=: y2)}
                                                        h2 : (pair . unpair) ~~ id {a=((x1, y1) :=: (x2, y2))}
dep_pair_id_destructor : {p : a -> Type} ->
                         {x1 : a} -> {x2 : a} -> {y1 : p x1} -> {y2 : p x2} -> 
                         ((x1 ** y1) :=: (x2 ** y2)) :~: (p : (x1 :=: x2) ** transport p y1 :=: y2) 
dep_pair_id_destructor {p=p} {x1=x1} {x2=x2} {y1=y1} {y2=y2} = qinv_to_equiv un_dep_pair (dep_pair ** (h1, h2))
                                                                 where
                                                                    dep_pair : (p : (x1 :=: x2) ** transport p y1 :=: y2) -> ((x1 ** y1) :=: (x2 ** y2))
                                                                    dep_pair (p1 ** p2) = cons_dpair_equ x1 y1 x2 y2 p1 p2
                                                                    un_dep_pair : ((x1 ** y1) :=: (x2 ** y2)) -> (p : (x1 :=: x2) ** transport p y1 :=: y2)
                                                                    h1 : (un_dep_pair . dep_pair) ~~ id {a=(p : (x1 :=: x2) ** transport p y1 :=: y2)}
                                                                    h2 : (dep_pair . un_dep_pair) ~~ id {a=(x1 ** y1) :=: (x2 ** y2)}
-- -- inject an equivalence
inject : isequiv {a=a} {b=b} f -> a :~: b
inject {f=f} e = (f ** e)

-- -- reflexive
refl : a :~: a
refl = inject $ id_equivalence

-- -- symmetric
rev : a :~: b -> b :~: a
rev {a=a} {b=b} (f ** e) =  (g ** e2)
                  where 
                  qinv_f : qinv f
                  qinv_f = isequiv_to_qinv e
                  g : b -> a
                  g = fst qinv_f 
                  h1 : (f . g) ~~ id {a=b}
                  h1 = fst $ snd qinv_f
                  h2 : (g . f) ~~ id {a=a}
                  h2 = snd $ snd qinv_f
                  f_is_inverse : qinv g
                  f_is_inverse = (f ** (h2, h1))
                  e2 : isequiv g
                  e2 = qinv_to_isequiv f_is_inverse


-- transitivity
infix 11 :~>: 
(:~>:) : a :~: b -> b :~: c -> a :~: c
(:~>:) (f ** e1) (g ** e2) = (g . f ** transitivity_equiv e1 e2)


-- finally, the univalence axion

univalence : (a :=: b) :~: (a :~: b)
-- it's an axiom, no implementation required!