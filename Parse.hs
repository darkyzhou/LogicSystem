module Parse where

import Prop 
import Text.ParserCombinators.Parsec 

propLine = prop <* manyTill space eol

-- 一个完整的命题
prop = do 
    p <- singleProp
    op <- optionMaybe propOperator
    case op of
        Nothing -> return p
        Just _op -> _op p <$> prop

-- 独立命题，即用括号包围的命题、非命题、命题变元和布尔常量
singleProp = spaces *> 
    (quotedProp <|> propNot <|> varProp) <*
    spaces

-- 用括号包围的命题
quotedProp = between (char '(') (char ')') prop 

-- 非命题
propNot = char '~' *> (Not <$> singleProp)

-- 命题变元和布尔常量
varProp = helper <$> anyChar 
    where helper 'T' = Const True 
          helper 'F' = Const False 
          helper c = Var [c]

-- 命题连接词
propOperator = strToConstructor <$> choice [try (string "/\\")
                                          , try (string "\\/")
                                          , try (string "->")
                                          , try (string "<->")
                                          ]
    where strToConstructor "/\\" = And
          strToConstructor "\\/" = Or
          strToConstructor "->" = Imply 
          strToConstructor "<->" = BiImply 

-- 注释
comment = string "\\\\" *> manyTill anyChar eol *> spaces

-- 换行
eol =   try (string "\n\r")
    <|> try (string "\r\n")
    <|> string "\n"
    <|> string "\r"
    <?> "Expected the end of a line."

-- 完整的形式证明
-- (aurgument::[Prop], Conclusion::Prop, proveStep::[([Prop], Prop, rule, [])])
prove = (,,) 
    <$> (spaces *> many comment *> string "Premises:" *> argument) 
    <*> (spaces *> many comment *> string "Conclusion:" *> conclusion) 
    <*> (spaces *> many comment *> string "Proof:" *> spaces *> many comment
                *> many1 (proveStep <* spaces <* many comment))

-- 形式证明的前提
argument = sepBy prop (char ',')

-- 形式证明的结论
conclusion = prop 

-- 一个推理步骤
-- (前提，结论，规则，[参数])
proveStep = (,,,)
    <$> (spaces *> many1 digit *> char '.' *> argument) 
    <* spaces <* string "|-" 
    <*> prop 
    <* char '['
    <* spaces
    <*> many1 (noneOf " ]") 
    <* spaces 
    <*> (map (\x -> read x::Int) <$> many (many1 digit <* spaces))
    <* char ']'

