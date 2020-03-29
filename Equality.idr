module Equality


%access public export

infixr 11 :=:
data (:=:) : a -> a -> Type where
	Reflexive : (x : a) -> (x :=: x)

-- Based path induction
-- this is more of an axion than a proposition
ind'' : (x : a) -> 
        (C : (y : a) -> (x :=: y) -> Type) ->
        (C x (Reflexive x)) ->
        (y : a) ->
        (p : x :=: y) -> (C y p)
ind'' x f c0 x (Reflexive x) = c0

-- Path induction
ind : {a : Type} ->
      (C : (x0 : a) -> (y0 : a) -> (x0 :=: y0) -> Type) ->
      ((x0 : a) -> C x0 x0 (Reflexive x0)) ->
      (x : a) ->
      (y : a) ->
      (p : x :=: y) -> (C x y p)
ind {a = a} c c0 x = ind'' x cons $ c0 x
             where
             cons : (u : a) -> (x :=: u) -> Type
             cons u p = c x u p



-- symmetry
rev : {x : a} -> {y : a} -> (x :=: y) -> (y :=: x)
rev {x=x} {y=y} = ind'' x aux (Reflexive x) y
                  where
                  aux : (u : a) -> (x :=: u) -> Type
                  aux u p = u :=: x

-- transitivity
infixr 11 :>:
(:>:) : {x : a} -> {y : a} -> {z : a} -> (x :=: y) -> (y :=: z) -> (x :=: z)
(:>:) {x=x} {y=y} {z=z} = ind'' x aux id y
                          where
                          aux : (u : a) -> (x :=: u) -> Type
                          aux u p = (u :=: z) -> (x :=: z)

-- applicative functor
fmap : {a : Type} ->
       {x : a} ->
       {y : a} -> 
       (f : a -> b) -> 
       (x :=: y) -> f x :=: f y
fmap {a = a} {x=x} {y=y} f = ind cons c0 x y
                      where
                      cons : (x0 : a) -> (y0 : a) -> (x0 :=: y0) -> Type
                      cons x0 y0 p = (f x0) :=: (f y0)
                      c0 : (x0 : a) -> (f x0) :=: (f x0)
                      c0 x0 = Reflexive $ f x0

-- applicative functor for dependent maps
dfmap : {a : Type} -> {p : a -> Type} -> 
        {x : a} ->
        {y : a} -> 
        (f : (x : a) -> p x) -> 
        (x :=: y) -> (x ** f x) :=: (y ** f y) -- path in the fibration
dfmap {a = a} {x=x} {y=y} f = ind cons c0 x y
                                where
                                cons : (x0 : a) -> (y0 : a) -> (x0 :=: y0) -> Type
                                cons x0 y0 p = (x0 ** f x0) :=: (y0 ** f y0)
                                c0 : (x0 : a) -> (x0 ** f x0) :=: (x0 ** f x0)
                                c0 x0 = Reflexive $ (x0 ** f x0)

-- transport
transport : {a : Type} -> {prop : a -> Type} -> 
            {x : a} -> {y : a} -> 
            (x :=: y) ->
            prop x -> prop y
transport {prop=prop} {x=x} {y=y} = ind cons c0 x y
                                      where
                                        cons : (x0 : a) -> (y0 : a) -> (x0 :=: y0) -> Type
                                        cons x0 y0 p = prop x0 -> prop y0
                                        c0 : (x0 : a) -> prop x0 -> prop x0
                                        c0 x0 = id
  


-- lift equality to functions
lift : {a : Type} -> 
       {b : Type} ->
       (f : a -> b) -> 
       (g : a -> b) -> 
       (f :=: g) -> ((x : a) -> ((f x) :=: (g x)) ) -- (p: f:=:g) -> cons f g p
lift {a=a} {b=b} f g p = ind cons c0 f g p
          where 
          cons : (f0 : a -> b) -> (g0 : a -> b) -> (f0 :=: g0) -> Type
          cons f0 g0 p = (x : a) -> ((f0 x) :=: (g0 x))
          --
          c0 : (f0 : a -> b) -> (x : a) -> (f0 x :=: f0 x) 
          c0 f0 x = Reflexive $ f0 x


-- pair equality
cons_pair_equ : (x : a) -> (y : b) ->
                (x1 : a) -> (y1 : b) ->
                (x :=: x1) -> (y :=: y1) ->
                ((x, y) :=: (x1, y1))
cons_pair_equ x y x1 y1 p1 p2 = fmap (\z => (x, z)) p2 :>:
                                          fmap (\z => (z, y1)) p1 

uncons_pair_equ : (x : a) -> (y : b) ->
                  (x1 : a) -> (y1 : b) ->
                  ((x, y) :=: (x1, y1)) ->
                  (x :=: x1, y :=: y1)
uncons_pair_equ x y x1 y1 p = (fmap fst p, fmap snd p) 

-- dependent pair equality
cons_dpair_equ : {prop : a -> Type} ->
                 (x : a) -> (y : prop x) ->
                 (x1 : a) -> (y1 : prop x1) ->
                 (p : x :=: x1) -> ((transport p y) :=: y1) ->
                 ((x ** y) :=: (x1 ** y1))
cons_dpair_equ {a=a} {prop=prop} x y x1 y1 p p1 = aux x1 p :>: fmap (\z => (x1 ** z)) p1
                                                    where
                                                    aux : (z : a) -> (p : x :=: z) ->
                                                          ((x ** y) :=: (z ** transport p y))
                                                    aux = ind'' x cons c0
                                                            where
                                                            cons : (x0 : a) -> (x :=: x0) -> Type
                                                            cons x0 p = (x ** y) :=: (x0 ** transport p y)
                                                            c0 : (x ** y) :=: (x ** transport (Reflexive x) y)
                                                            c0 = Reflexive (x ** y)
                                                                      


