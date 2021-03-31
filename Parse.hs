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

-- (结论，（规则，[前件]）)
proveStep = (,,)
    <$> (spaces *> many1 digit *> char '.' *> prop) 
    <* char '['
    <*> many1 (noneOf ",]")
    <*> (map (\x -> read x::Int) <$> many (char ',' *> many1 digit))
    <* char ']'

proveSteps = count 5 proveStep 
    where proveStep = do 
            spaces *> many1 digit *> char '.'
            pre <- sepBy prop (char ',')
            spaces *> string "!|-" *> spaces
            p <- prop 
            spaces *> string "["
            rule <- many1 $ noneOf ",]"
            d <- many (char ',' *> many1 digit)
            string "]" <?> "no ]"
            return (pre, p, rule, [read x::Int | x <- d])



