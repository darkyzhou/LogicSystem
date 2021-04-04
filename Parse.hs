module Parse where

import Prop 
import Text.ParserCombinators.Parsec 

propLine = prop <* manyTill space eol

prop = do 
    p <- singleProp
    op <- optionMaybe propOperator
    case op of
        Nothing -> return p
        Just _op -> _op p <$> prop

singleProp = spaces *> 
    (quotedProp <|> propNot <|> varProp) <*
    spaces

quotedProp = between (char '(') (char ')') prop 

propNot = char '~' *> (Not <$> singleProp)

varProp = helper <$> anyChar 
    where helper 'T' = Const True 
          helper 'F' = Const False 
          helper c = Var [c]

propOperator = strToConstructor <$> choice [try (string "/\\")
                                          , try (string "\\/")
                                          , try (string "->")
                                          , try (string "<->")
                                          ]
    where strToConstructor "/\\" = And
          strToConstructor "\\/" = Or
          strToConstructor "->" = Imply 
          strToConstructor "<->" = BiImply 

comment = string "\\\\" *> manyTill anyChar eol *> spaces

eol =   try (string "\n\r")
    <|> try (string "\r\n")
    <|> string "\n"
    <|> string "\r"
    <?> "Expected the end of a line."


-- (aurgument::[Prop], Conclusion::Prop, proveStep::[([Prop], Prop, rule, [])])

prove = (,,) 
    <$> (spaces *> many comment *> string "Premises:" *> argument) 
    <*> (spaces *> many comment *> string "Conclusion:" *> conclusion) 
    <*> (spaces *> many comment *> string "Proof:" *> spaces *> many comment
                *> many1 (proveStep <* spaces <* many comment))

argument = sepBy prop (char ',')

conclusion = prop 

-- (前件，后件，规则，[参数])
proveStep = (,,,)
    <$> (spaces *> many1 digit *> char '.' *> argument) 
    <* spaces <* string "|-" 
    <*> prop 
    <* char '['
    <*> many1 (noneOf " ]")
    <*> (map (\x -> read x::Int) <$> many (spaces *> many1 digit))
    <* char ']'

