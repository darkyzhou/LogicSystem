module Func where

import Prop 
import Text.Printf

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
    notElem Nothing dpItems && itemCompare pItems (map (\(Just s) -> s) dpItems)
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

-- ********************************************
-- 证明过程验证库函数
-- (aurgument::[Prop], Conclusion::Prop, proveStep::[([Prop], Prop, rule, [])])

validate :: ([Prop], Prop, [([Prop], Prop, String, [Int])]) -> (Bool, String) 
validate (arg, conclusion, steps) = if (arg, conclusion) /= (\(a, b, _, _) -> (a, b)) (last steps) then 
                                    (False, "The final step does NOT fit the form that deducing \"Conclusion\" from \"Premises\".")
                                    else 
                                    validateSteps steps 0

validateSteps :: [([Prop], Prop, String, [Int])] -> Int -> (Bool, String) 
validateSteps steps k 
    | k == length steps = (True, "") 
    | otherwise = case validateStep (take k steps) curStep of 
                (True, "")   -> validateSteps steps (k+1)
                (False, msg) -> (False, printf "Fail in validating step %d.\n%s" (k+1) msg)
    where curStep = steps!!k 

validateStep :: [([Prop], Prop, String, [Int])] -> ([Prop], Prop, String, [Int]) -> (Bool, String) 
validateStep steps (argument, conclusion, rule, param)
    | rule == "prem" = func0 prem
    | rule == "premi" = func1 premi
    | rule == "preme" = func2 preme
    | rule == "ti" = func0 ti
    | rule == "fi" = func0 fi
    | rule == "ori" = func1 ori
    | rule == "ore" = func2 ore
    | rule == "andi" = func2 andi 
    | rule == "ande" = func1 ande 
    | rule == "impli" = func1 impli
    | rule == "imple" = func2 imple 
    | rule == "ni" = func2 ni 
    | rule == "ne" = func2 ne
    | rule == "nni" = func1 nni 
    | rule == "nne" = func1 nne
    | rule == "equivi" = func2 equivi 
    | rule == "equive" = func1 equive
    | rule == "implyToOr" = func1 implyToOr 
    | rule == "orToImply" = func1 orToImply
    | rule == "orThree" = func2 orThree
    | rule == "morgane" = func1 morgane
    | rule == "morgani" = func1 morgani
    | otherwise = (False, printf "Unknown rule: \"%s\"" rule)

    where p1 = getParam steps param 0
          p2 = getParam steps param 1
          biCall func p1 p2 arg c = func p1 p2 arg c || func p2 p1 arg c
          func0 f 
            | not $ null param = (False, printf "\"%s\": need no parameter, but found %d." rule (length param))
            | f argument conclusion = (True, "")
            | otherwise = (False, printf "\"%s\": found invalid parameter(s)." rule)
          func1 f 
            | length param /= 1 = (False, printf "\"%s\": need 1 parameter, but found %d." rule (length param))
            | otherwise = case p1 of 
                (Just a) -> if f a argument conclusion then (True, "") 
                            else (False, printf "\"%s\": cannot deduce the given proposition." rule)
                _        -> (False, printf "\"%s\": found invalid parameter(s)." rule)
          func2 f 
            | length param /= 2 = (False, printf "\"%s\": need 2 parameters, but found %d." rule (length param))
            | otherwise = case (p1, p2) of 
                (Just a, Just b) -> if biCall f a b argument conclusion then (True, "") 
                                    else (False, printf "\"%s\": cannot deduce the given proposition." rule)
                _                -> (False, printf "\"%s\": found invalid parameter(s)." rule)
    
    
getParam steps param k 
    | (k<length param) && (idx>=0) && (idx<length steps) = Just ((\(a, b, _, _) -> (a, b)) (steps !! idx))
    | otherwise = Nothing 
    where idx = (param!!k) - 1 


-- ****************************************************
-- 推导规则

prem :: [Prop] -> Prop -> Bool
prem arg p = p `elem` arg

premi :: ([Prop], Prop) -> [Prop] -> Prop -> Bool 
premi (pre1, c1) pre c = (pre1 == init pre) && (c1 == c)

preme :: ([Prop], Prop) -> ([Prop], Prop) -> [Prop] -> Prop -> Bool 
preme (pre1, c1) (pre2, c2) pre c = (ip1 == ip2) && (Not lp1 == lp2) && (c1 == c2) && (pre == ip1) && (c1 == c) 
    where ip1 = init pre1 
          ip2 = init pre2 
          lp1 = last pre1 
          lp2 = last pre2

ti :: [Prop] -> Prop -> Bool 
ti _ p = p == Const True

fi :: [Prop] -> Prop -> Bool 
fi _ p = p == Not (Const False)

ori :: ([Prop], Prop) -> [Prop] -> Prop -> Bool 
ori (pre1, c1) pre (Or a b) = (pre1==pre) && ((c1==a) || (c1==b))
ori _ _ _ = False 

ore :: ([Prop], Prop) -> ([Prop], Prop) -> [Prop] -> Prop -> Bool 
ore (pre1, c1) (pre2, c2) pre c = (ip1==ip2) && (c1==c2) && (c1==c) && (ip1==ip) && 
                                  ((Or lp1 lp2 == lp) || (Or lp2 lp1 == lp))
    where ip1 = init pre1 
          ip2 = init pre2 
          lp1 = last pre1 
          lp2 = last pre2
          ip = init pre 
          lp = last pre

andi :: ([Prop], Prop) -> ([Prop], Prop) -> [Prop] -> Prop -> Bool 
andi (pre1, c1) (pre2, c2) pre c = (pre1==pre2) && (pre1==pre) && ((And c1 c2 == c) || (And c2 c1 == c))

ande :: ([Prop], Prop) -> [Prop] -> Prop -> Bool 
ande (pre1, And a b) pre c = (pre1==pre) && ((a==c) || (b==c))
ande _ _ _ = False 

impli :: ([Prop], Prop) -> [Prop] -> Prop -> Bool 
impli (pre1, c1) pre c = (init pre1 == pre) && (Imply (last pre1) c1 == c)

imple :: ([Prop], Prop) -> ([Prop], Prop) -> [Prop] -> Prop -> Bool 
imple (pre1, c1) (pre2, c2) pre c = (pre1==pre) && (pre2==pre) && (Imply c1 c == c2)

ni :: ([Prop], Prop) -> ([Prop], Prop) -> [Prop] -> Prop -> Bool 
ni (pre1, c1) (pre2, c2) pre c = (pre1==pre2) && (Not c1 == c2) && (Not (last pre1) == c)

ne :: ([Prop], Prop) -> ([Prop], Prop) -> [Prop] -> Prop -> Bool 
ne (pre1, c1) (pre2, c2) pre c = (pre1==pre2) && (pre1==pre) && (Not c1 == c2)

nni :: ([Prop], Prop) -> [Prop] -> Prop -> Bool 
nni (pre1, c1) pre c = Not (Not c1) == c

nne :: ([Prop], Prop) -> [Prop] -> Prop -> Bool 
nne (pre1, c1) pre c = Not (Not c) == c1

equivi :: ([Prop], Prop) -> ([Prop], Prop) -> [Prop] -> Prop -> Bool 
equivi (pre1, c1) (pre2, c2) pre c = (ip1==ip2) && (lp1==c2) && (lp2==c1) && (ip1==pre) && 
                                     (BiImply c1 c2 == c)
    where ip1 = init pre1 
          ip2 = init pre2 
          lp1 = last pre1 
          lp2 = last pre2

equive :: ([Prop], Prop) -> [Prop] -> Prop -> Bool 
equive (pre1, BiImply a b) pre c = (pre1==pre) && ((Imply a b == c) || (Imply b a == c))
equive _ _ _ = False

implyToOr :: ([Prop], Prop) -> [Prop] -> Prop -> Bool 
implyToOr (pre1, Imply a b) pre c = (pre1==pre) && ((Or (Not a) b == c) || (Or b (Not a) == c))
implyToOr _ _ _ = False 

orToImply :: ([Prop], Prop) -> [Prop] -> Prop -> Bool 
orToImply (pre1, Or (Not a) b) pre (Imply c d) = (pre1==pre) && (a==c) && (b==d)
orToImply (pre1, Or b (Not a)) pre (Imply c d) = (pre1==pre) && (a==c) && (b==d)
orToImply _ _ _ = False 

orThree :: ([Prop], Prop) -> ([Prop], Prop) -> [Prop] -> Prop -> Bool 
orThree (pre1, Or (Not a) b) (pre2, c) pre d = (pre1==pre2) && (pre1==pre) && (a==c) && (b==d)
orThree (pre1, Or b (Not a)) (pre2, c) pre d = (pre1==pre2) && (pre1==pre) && (a==c) && (b==d)
orThree _ _ _ _ = False 

morgani :: ([Prop], Prop) -> [Prop] -> Prop -> Bool 
morgani (pre1, Not (Or a b)) pre c = (pre1==pre) && (And (Not a) (Not b) == c)
morgani (pre1, Not (And a b)) pre c = (pre1==pre) && (Or (Not a) (Not b) == c)
morgani _ _ _ = False 

morgane :: ([Prop], Prop) -> [Prop] -> Prop -> Bool 
morgane (pre1, c) pre (Not (Or a b)) = (pre1==pre) && (And (Not a) (Not b) == c)
morgane (pre1, c) pre (Not (And a b)) = (pre1==pre) && (Or (Not a) (Not b) == c)
morgane _ _ _ = False 