module Prop  (
    Prop(..),
    Subst(..),
    eval, -- :: Subst -> Prop -> Bool
    vars, -- :: Prop -> [Char]
    substs, -- :: Prop -> [Subst]
    isTaut, -- :: Prop -> Bool
    isEquiv, -- Prop -> Prop -> Bool
) where

import Data.List ( nub )

data Prop = Const Bool
          | Var String
          | Not Prop
          | And Prop Prop
          | Or Prop Prop
          | Imply Prop Prop
          | BiImply Prop Prop
          deriving Eq

type Subst = [(String, Bool)]

-- Prop类型输出
instance Show Prop where
    show (Const True) = "T"
    show (Const False) = "F"
    show (Var c) =  c
    show (Not (Const t)) = "~" ++ show t
    show (Not (Var x))    = "~" ++ x
    show (Not p) = "~" ++ show p
    show (And a b) = "(" ++ show a ++ "∧" ++ show b ++")"
    show (Or a b) =  "(" ++ show a ++ "∨" ++ show b ++")"
    show (Imply a b) =  "(" ++ show a ++ "->" ++ show b ++")"
    show (BiImply a b) =  "(" ++ show a ++ "<->" ++ show b ++")"

-- 接收一个Prop和相应的取值集合，判断Prop的取值
eval :: Subst -> Prop -> Bool
eval _ (Const b) = b
eval s (Var a) = snd $ head $ dropWhile (\(x, _) -> x /= a) s
eval s (Not p) = not $ eval s p
eval s (And p q) = (eval s p) && (eval s q)
eval s (Or p q) = (eval s p) || (eval s q)
eval s (Imply p q) = (not (eval s p)) || (eval s q)
eval s (BiImply p q) = (eval_p && eval_q) || ((not eval_p) && (not eval_q))
    where eval_p = eval s p
          eval_q = eval s q

-- 获取一个Prop的所有命题变元
vars :: Prop -> [String]
vars (Const _) = []
vars (Var v) = [v]
vars (Not p) = vars p
vars (And p q) = nub(vars p ++ vars q)
vars (Or p q) = nub(vars p ++ vars q)
vars (Imply p q) = nub(vars p ++ vars q)
vars (BiImply p q) = nub(vars p ++ vars q)

-- 获取一个Prop所有的可能的变元取值集合
-- [[(String, Bool)]]
substs :: Prop -> [Subst]
substs p = helper $ vars p
    where helper [] = []
          helper [x] = [[(x, True)], [(x, False)]]
          helper (x : xs) = [(x, True) : s | s <- sxs] ++ [(x, False) : s | s <- sxs]
            where sxs = helper xs

-- 判断是否为永真式
isTaut :: Prop -> Bool
isTaut p = all (`eval` p) (substs p)

-- 判断两个命题是否等值
isEquiv :: Prop -> Prop -> Bool
isEquiv p q = isTaut $ BiImply p q

