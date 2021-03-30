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

quotedProp = char '(' *> prop <* char ')' 

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

prove = do 
    spaces *> string "Argument:"
    ar <- argument 
    spaces *> string "Conclusion:"
    con <- conclusion 
    spaces *> string "Proof."
    prove <- proveSteps <?> "fail in prove parse."
    spaces *> string "Qed."
    return (ar, con, prove)

argument = sepBy prop (char ',')

conclusion = prop 

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



