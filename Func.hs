module Func where

import Prop 

-- **********************************
-- 主析取范式验证库函数

-- 先对目标命题进行解析，再求原命题的最小项，并与解析结果比较
disjunctiveNormValidate :: Prop -> Prop -> Bool 
disjunctiveNormValidate p dp = 
    (not $ elem Nothing dpItems) && (itemCompare pItems $ map (\(Just s) -> s) dpItems)
    where pItems = disjunctiveNorm p
          dpItems = map (propToSubst . conjuncResolve) $ disjuncResolve dp
          propToSubst (x:xs) = case x of
              Var s -> helper (s, True) (propToSubst xs)
              (Not (Var s)) -> helper (s, False) (propToSubst xs)
              _ -> Nothing
          propToSubst [] = Just []
          helper x (Just xs) = Just (x:xs)
          helper x Nothing = Nothing

-- 对命题进行析取解析，即将析取转换为列表
-- 如 q /\ p 转换为 [q, p]
disjuncResolve :: Prop -> [Prop]
disjuncResolve (Or p q) = (disjuncResolve p) ++ (disjuncResolve q)
disjuncResolve p = [p]

-- 对命题进行合取解析，即将合取转换为列表
-- 如 q \/ p 转换为 [q, p]
conjuncResolve :: Prop -> [Prop]
conjuncResolve (And p q) = (conjuncResolve p) ++ (conjuncResolve q)
conjuncResolve p = [p]

-- 求主析取范式，返回形式为最小项的列表
disjunctiveNorm :: Prop -> [Subst]
disjunctiveNorm p = filter (`eval` p) (substs p)

-- 比较两种解析结果是否一致
-- 忽略列表中命题的顺序
itemCompare :: [Subst] -> [Subst] -> Bool 
itemCompare a b = (qsort sa) == (qsort sb)
    where sa = map qsort a 
          sb = map qsort b

-- 快速排序
qsort :: Ord a => [a] -> [a]
qsort l@(h:t) = qsort (filter (<h) t) ++ filter (==h) l ++ qsort (filter (>h) t)
qsort [] = []

-- **********************************
-- 主析取范式验证库函数

-- 先对目标命题进行解析，再求原命题的最大项，并与解析结果比较
conjunctiveNormValidate :: Prop -> Prop -> Bool 
conjunctiveNormValidate p dp = 
    (not $ elem Nothing dpItems) && (itemCompare pItems $ map (\(Just s) -> s) dpItems)
    where pItems = conjunctiveNorm p
          dpItems = map (propToSubst . disjuncResolve) $ conjuncResolve dp
          propToSubst (x:xs) = case x of
              Var s -> helper (s, True) (propToSubst xs)
              (Not (Var s)) -> helper (s, False) (propToSubst xs)
              _ -> Nothing
          propToSubst [] = Just []
          helper x (Just xs) = Just (x:xs)
          helper x Nothing = Nothing

conjunctiveNorm :: Prop -> [Subst] 
conjunctiveNorm p = map helper $ filter (not . (`eval` p)) (substs p)
    where helper ((s, True):xs) = (s, False) : helper xs
          helper ((s, False):xs) = (s, True) : helper xs
          helper [] = []

-- Library for prove
-- (aurgument::[Prop], Conclusion::Prop, proveStep::[([Prop], Prop, rule, [])])

prem :: [Prop] -> Prop -> Bool
prem arg p = p `elem` arg

imple :: Prop -> Prop -> Prop -> Bool 
imple (Imply _p1 _p2) p1 p2 = (isEquiv _p1 p1) && (isEquiv _p2 p2) 
imple p1 (Imply _p1 _p2) p2 = (isEquiv _p1 p1) && (isEquiv _p2 p2) 
imple _ _ _ = False

ni :: [Prop] -> Prop -> Prop -> Prop -> Bool 
ni arg p1 p2 p3 = (isEquiv p1 $ Not p2) && any (isEquiv $ Not p3) arg

validate :: ([Prop], Prop, [([Prop], Prop, String, [Int])]) -> Bool 
validate (arg, conclusion, steps) = conclusion == (\(_, a, _, _) -> a) (last steps)
                                    && validateSteps arg steps [] 0

validateSteps :: [Prop] -> [([Prop], Prop, String, [Int])] -> [Prop] -> Int -> Bool 
validateSteps arg steps result k 
    | k == length steps = True 
    | otherwise = validateStep arg curStep result
                  && validateSteps arg steps (result++[curConclusion]) (k+1)
    where curStep = steps!!k 
          curConclusion = (\(_, a, _, _) -> a) curStep 

validateStep :: [Prop] -> ([Prop], Prop, String, [Int]) -> [Prop] -> Bool 
validateStep arg (pre, conclusion, rule, param) result 
    | rule == "prem" = prem pre conclusion
    | rule == "imple" = imple (result!!((param!!0)-1)) (result!!((param!!1)-1)) conclusion
    | rule == "ni" = ni pre (result!!((param!!0)-1)) (result!!((param!!1)-1)) conclusion