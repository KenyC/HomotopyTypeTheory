module Natural

import Equality

data Natural = Zero | Succ Natural

induction : (P : Natural -> Type) ->
            (P Zero) -> 
            ((n : Natural) -> P n -> (P $ Succ n)) ->
            (n : Natural) -> P n
induction P x f Zero = x
induction P x f (Succ n) = f n $ induction P x f n

-- Addition
infixr 12 :+:
(:+:) : Natural  -> Natural -> Natural
(:+:) Zero n = n
(:+:) (Succ m) n = Succ (m :+: n)


-- Associativity of addition
-- x = 0 + x
aux1 : (x : Natural) -> x :=: (Zero :+: x)
aux1 = Reflexive

-- (x + 1) + y = (x + y) + 1 
aux2 : (x : Natural) -> (y : Natural) ->
        (((Succ x) :+: y) :=: Succ (x :+: y))
aux2 x y = Reflexive $ Succ $ x :+: y

-- (x + y) + 1 = (x + 1) + y -- rev aux2
aux3 : (x : Natural) -> (y : Natural) ->
        (Succ (x :+: y) :=: ((Succ x) :+: y))
aux3 x y = rev $ aux2 x y

associativity : (x : Natural) -> (y : Natural) -> (z : Natural) -> 
                (x :+: (y :+: z)) :=: ((x :+: y) :+: z)
associativity x y z = induction property basecase inheritance x
                   where
                   property : Natural -> Type
                   property x0 = (x0 :+: (y :+: z)) :=: ((x0 :+: y) :+: z)
                   ----
                   -- 0 + (y + z) = y + z       -- rev aux1
                   -- y + z = (0 + y) + z       -- fmap (:+: z) aux1
                   -- 0 + (y + z) = (0 + y) + z --
                   basecase : {y0 : Natural} -> {z0 : Natural} ->
                              (Zero :+: (y0 :+: z0)) :=: ((Zero :+: y0) :+: z0)
                   basecase {y0=y0} {z0=z0} = (rev $ aux1 $ y0 :+: z0) :>: (fmap (:+: z0) (aux1 $ y0))
                   ----
                   -- (x + 1) + (y + z) = (x + (y + z)) + 1       -- aux2
                   -- (x + (y + z)) + 1 = ((x + y) + z) + 1       -- fmap Succ rec
                   -- ((x + y) + z) + 1 = ((x + y) + 1) + z       -- (rev aux2)
                   -- (((x + y) + 1) + z) = ((x + 1) + y) + z     -- fmap (:+: z) (rev aux2)
                   inheritance :  {y0 : Natural} -> {z0 : Natural} -> (x0 : Natural) ->
                                 ((x0 :+: (y0 :+: z0)) :=: ((x0 :+: y0) :+: z0)) ->
                                 (((Succ x0) :+: (y0 :+: z0)) :=: (((Succ x0) :+: y0) :+: z0))
                   inheritance {y0 = y0} {z0 = z0} x0 rec = 
                               (aux2 x0 $ y0 :+: z0) :>:
                               (fmap Succ rec) :>:
                               (aux3 (x0 :+: y0) z0) :>:
                               (fmap (:+: z0) $ aux3 x0 y0)

aux4 : (x : Natural) ->
		x :=: x :+: Zero

aux4 x = induction property basecase inheritance x
           where
           property : Natural -> Type
           property x0 = x0 :=: x0 :+: Zero
           ---
           basecase : (Zero :+: Zero) :=: Zero
           basecase = Reflexive Zero
           ----
           inheritance : (x0 : Natural) ->
                         (x0  :=: x0 :+: Zero) ->
                         (Succ x0 :=: Succ x0 :+: Zero)
           inheritance n rec = fmap Succ rec

aux5 : (x : Natural) ->
		Succ x :=: x :+: (Succ Zero)
aux5 x = induction property basecase inheritance x
           where
           property : Natural -> Type
           property x0 = Succ x0 :=: x0 :+: (Succ Zero)
           ---
           basecase : Succ Zero :=: Zero :+: Succ Zero
           basecase = Reflexive $ Succ Zero
           ----
           -- succ (succ x0) = succ (x0 + succ 0) 
           inheritance : (x0 : Natural) ->
                         (Succ x0  :=: x0 :+: Succ Zero) ->
                         (Succ (Succ x0) :=: Succ x0 :+: Succ Zero)
           inheritance x0 rec = fmap Succ rec :>: (aux3 x0 $ Succ Zero)


commutativity : (x : Natural) -> (y : Natural) ->
                x :+: y :=: y :+: x
commutativity x y = induction property basecase inheritance x
                       where
                       property : Natural -> Type
                       property x0 = (x0 :+: y) :=: (y :+: x0)
                       ----
                       -- 0 + y = y       -- rev aux1
                       -- y = y + 0       -- aux4
                       basecase : (Zero :+: y) :=: (y :+: Zero)
                       basecase = (rev $ aux1 y) :>: (aux4 y)
                       ----
                       -- (x + 1) + y = (x + y) + 1       -- aux2
                       -- (x + y) + 1 = (y + x) + 1       -- fmap Succ rec
                       -- (y + x) + 1 = y + (x + 1) =     -- (rev associativity)
                       -- rev aux5
                       inheritance : (x0 : Natural) ->
                                     (x0 :+: y :=: y :+: x0) ->
                                     (Succ x0 :+: y :=: y :+: Succ x0)
                       inheritance x0 rec = 
                                   aux2 x0 y :>:
                                   fmap Succ rec :>:
                                   aux5 (y :+: x0) :>:
                                   rev (associativity y x0 $ Succ Zero) :>:
                                   (fmap ((:+:) y) $ rev $ aux5 x0)




