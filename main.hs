{-# LANGUAGE FlexibleContexts #-}
import Control.Monad.Except
import Data.List

-- Part 1

type Symb = String 
infixl 2 :@

data Expr = Var Symb
          | Expr :@ Expr
          | Lam Symb Expr
          deriving (Eq, Read, Show)


freeVars :: Expr -> [Symb]
freeVars (Var x)                 = [x]
freeVars (e1 :@ e2)              = freeVars e1 ++ freeVars e2
freeVars (Lam x e) | elem x list = filter (/= x) list 
                   | otherwise   = list
    where list = freeVars e

subst :: Symb -> Expr -> Expr -> Expr 
subst v n (Var x) | v == x    = n
                  | otherwise = (Var x)
subst v n (e1 :@ e2) = (subst v n e1) :@ (subst v n e2)
subst v n (Lam y e) | v == y           = (Lam y e)
                    | elem y frVarsN   = (Lam z $ subst v n (subst y (Var z) e))
                    | otherwise        = (Lam y $ subst v n e) 
    where z = (findNewVar y)
          findNewVar cur | and [(not (elem newCur frVarsE)), (not (elem newCur frVarsN))] = newCur
                         | otherwise                                                      = findNewVar newCur
                    where newCur = cur ++ ['\'']                  
          frVarsE = freeVars e
          frVarsN = freeVars n                  


t1 = Lam "x" $ (Var "x") :@ (Var "y")
t2 = Lam "x" $ (Var "z") :@ (Var "y")
t3 = (Var "z") :@ (Lam "x" $ (Var "z") :@ (Var "y"))

-- Part 2

infix 1 `alphaEq`

alphaEq :: Expr -> Expr -> Bool
alphaEq (Var x) (Var y)                   = x == y
alphaEq (e1 :@ e2) (e1' :@ e2')           = and [(alphaEq e1 e1'), (alphaEq e2 e2')]
alphaEq (Lam x e1) (Lam y e2) | x == y    = alphaEq e1 e2
                              | otherwise = alphaEq (subst x (Var z) e1) (subst y (Var z) e2)
    where z = (findNewVar x)
          findNewVar cur | and [(not (elem newCur frVarsE)), (not (elem newCur frVarsN))] = newCur
                         | otherwise                                                      = findNewVar newCur
                    where newCur = cur ++ ['\'']                  
          frVarsE = freeVars e1
          frVarsN = freeVars e2  
alphaEq _ _ = False


-- Part 3

-- Функция freeTVars возвращает список свободных переменных типа (в STT все переменные типа свободные)
freeTVars :: Type -> [Symb]
freeTVars (TVar x)  = [x]
freeTVars (x :-> y) = union (freeTVars x) (freeTVars y)

-- Функция extendEnv расширяет контекст переменной с заданным типом
extendEnv :: Env -> Symb -> Type -> Env
extendEnv (Env xs) x t = Env $ (x, t) : xs

-- Функция freeTVarsEnv возвращает список свободных типовых переменных контекста
freeTVarsEnv :: Env -> [Symb]
freeTVarsEnv (Env xs) = nub $ concat $ map freeTVars $ map snd xs


-- Part 4

-- Тип
data Type = TVar Symb 
          | Type :-> Type
  deriving (Eq,Show)

-- Контекст
newtype Env = Env [(Symb,Type)]
  deriving (Eq,Show)

-- Подстановка
newtype SubsTy = SubsTy [(Symb, Type)]
  deriving (Eq,Show)

-- Функция appEnv, позволяющую использовать контекст как частичную функцию из переменных в типы
appEnv :: (MonadError String m) => Env -> Symb -> m Type
appEnv (Env []) v                      = throwError $ "There is no variable \"" ++ v ++ 
                                                                "\" in the enviroment."
appEnv (Env ((s, t):xs)) v | s == v    = return t
                           | otherwise = appEnv (Env xs) v

-- Part 5

-- Функции, осуществляющие подстановку типов вместо переменных типа в тип (appSubsTy) 
-- и подстановку типов вместо переменных типа в контекст (appSubsEnv):


appSubsTy :: SubsTy -> Type -> Type
appSubsTy (SubsTy l) (TVar s) = helper $! lookup s l
    where
        helper Nothing  = TVar s
        helper (Just x) = x                
appSubsTy s (x :-> y) = (appSubsTy s x) :-> (appSubsTy s y)

appSubsEnv :: SubsTy -> Env -> Env
appSubsEnv l (Env x) = Env $ map helper x
    where helper (f, s) = (f, appSubsTy l s)

-- Part 6

-- Функция composeSubsTy, выполняющую композицию двух подстановок 
-- (носитель композиции является объединением носителей двух этих подстановок)

composeSubsTy :: SubsTy -> SubsTy -> SubsTy
composeSubsTy (SubsTy f) (SubsTy s) = SubsTy $ map (go (SubsTy f)) $ map (go (SubsTy s)) helper
        where 
            helper = map (\el -> (el, TVar el)) vars
                where vars = union (map fst f) (map fst s)
            go subsT (x, y) = (x, appSubsTy subsT y)

instance Semigroup SubsTy where
    (<>) = composeSubsTy

instance Monoid SubsTy where
  mempty = SubsTy []
  mappend = (<>) 


-- Part 7

-- Реализуйте алгоритм унификации, возвращающий для двух переданных типов наиболее общий унификатор 
-- или сообщение об ошибке, если унификация невозможна.

unify :: MonadError String m => Type -> Type -> m SubsTy
unify (TVar x) (TVar y) | x /= y = return (SubsTy [(x, TVar y)])
                        | x == y = return mempty
unify (TVar x) t        | elem x $! freeTVars t = throwError ("Can't unify ( TVar " ++ show x 
                                                        ++ ") with (" ++ show t ++ ")!")
                        | otherwise             = return (SubsTy $ zip [x] [t])
unify (x1 :-> x2) (y1 :-> y2) = do res1 <- unify x2 y2
                                   res2 <- unify (appSubsTy res1 x1) (appSubsTy res1 y1)
                                   return (res1 <> res2)
unify s var = unify var s
