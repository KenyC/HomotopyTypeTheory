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
transitivity_equiv {f=f} {g=g} (f_inv_l ** (f_inv_r ** (hl, hr))) 
                               (g_inv_l ** (g_inv_r ** (hl'', hr''))) = (f_inv_l . g_inv_l ** (f_inv_r . g_inv_r ** ?hole))


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


-- -- type equivalence
infix 10 :~: 
(:~:) : Type -> Type -> Type 
(:~:) a b = (f : (a -> b) ** isequiv f)

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