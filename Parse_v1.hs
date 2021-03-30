module Parse where

import Prop 
import Text.ParserCombinators.Parsec 

propLine = prop <* manyTill space eol <* eol

prop = spaces *> 
    (quotedProp <|> propNot <|> notQuotedProp)

quotedProp = do
    char '('
    p <- prop
    spaces *> char ')'
    spaces
    op <- optionMaybe propOperator
    case op of
        Nothing -> return p 
        Just _op -> _op p <$> prop

propNot = do
    char '~' *> spaces
    Not <$> prop

notQuotedProp = do
    w <- propWord <|> propConst
    spaces
    op <- optionMaybe propOperator
    case op of
        Nothing -> return $ changeWord w 
        Just _op -> _op (changeWord w) <$> prop
    where changeWord 'T' = Const True 
          changeWord 'F' = Const False 
          changeWord s = Var [s]

propOperator = strToConstructor <$> choice [string "&&"
                                          , string "||"
                                          , string "->"
                                          , string "<->"
                                          ]
    where strToConstructor "&&" = And
          strToConstructor "||" = Or
          strToConstructor "->" = Imply 
          strToConstructor "<->" = BiImply 



propWord = (choice . map char $ ['A'..'E'])
    <?> "Expected a valid proposition variable."

propConst = char 'T' <|> char 'F'
    <?> "Expected a valid const variable"

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



