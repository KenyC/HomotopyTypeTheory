module TypeClasses

data TypeClass : Type where
	Class : (Type -> Type) -> TypeClass


belongs_to : Type -> TypeClass -> Type
belongs_to a (Class cons) = cons a


magma : TypeClass
magma = Class (\a => a -> a -> a)  

eq  : TypeClass            
eq = Class (\a => a -> a -> Bool)  

-- conditional implementation 
-- if a belongs to Eq, so does List a
-- eq_list : (a `belongs_to` eq) -> (List a `belongs_to` eq)
-- eq_list eq [] [] = True
-- eq_list eq l [] = False
-- eq_list eq [] l = False
-- eq_list eq (x::l) (y::l'')  = (x `eq` y) and (eq_list eq l l'')
