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

propOperator = strToConstructor <$> choice [string "/\\"
                                          , string "\\/"
                                          , string "->"
                                          , string "<->"
                                          ]
    where strToConstructor "/\\" = And
          strToConstructor "\\/" = Or
          strToConstructor "->" = Imply 
          strToConstructor "<->" = BiImply 

eol =   try (string "\n\r")
    <|> try (string "\r\n")
    <|> string "\n"
    <|> string "\r"
    <?> "Expected the end of a line."


-- (aurgument::[Prop], Conclusion::Prop, proveStep::[([Prop], Prop, rule, [])])

prove = (,,) 
    <$> (spaces *> string "Argument:" *> argument) 
    <*> (spaces *> string "Conclusion:" *> conclusion) 
    <*> (spaces *> string "Proof:" *> many1 (proveStep <* spaces))
    -- <* (spaces *> string "Qed.")

argument = sepBy prop (char ',')

conclusion = prop 

-- (前件，后件，规则，[参数])
proveStep = (,,,)
    <$> (spaces *> many1 digit *> char '.' *> many prop) 
    <* string "|-" 
    <*> prop 
    <* char '['
    <*> many1 (noneOf " ]")
    <*> (map (\x -> read x::Int) <$> many (char ' ' *> many1 digit))
    <* char ']'

