module Main where 
import Func 
import Prop
import Parse
import Text.ParserCombinators.Parsec 
import System.Environment
import System.Exit
import Text.Printf


main = do 
    args <- getArgs
    if null args then 
        putStrLn "ERROR: found no argument.\n"
    else if (head args /= "help") && (length args < 2) then 
        putStrLn $ printf "ERROR: need 2 arguments, but found %d.\n" (length args)
    else 
        case head args of 
            "equiv" -> equivJudge (args!!1)
            "dnorm" -> normJudge disjunctiveNormValidate "the principal disjunctive normal form" (args!!1)
            "cnorm" -> normJudge conjunctiveNormValidate "the principal conjunctive normal form" (args!!1)
            "validate" -> validateJudge (args!!1)
            "help" -> helpInfo
            s -> syntaxError s

-- 读取两个命题，判断是否等价
equivJudge path = do 
    text <- readFile path 
    case parse (many prop) path text of 
        (Left e) -> do 
            putStrLn "Error: fail in parsing the text into two propositions!"
            print e 
            putStrLn ""
            exitSuccess 
        (Right ps) -> 
            if length ps < 2 then 
                putStrLn $ printf "ERROR: need two propositions, but found %d.\n" (length ps)
            else do 
                let (a:(b:_)) = ps
                if isEquiv a b then 
                    putStrLn "True: The given proposition IS equivalent.\n"
                else 
                    putStrLn "FALSE: The given proposition IS NOT equivalent.\n"

-- 读取两个命题，判断第二个是不是第一个的主析取（合取）范式
normJudge func descrip path = do 
    text <- readFile path 
    case parse (many prop) path text of 
        (Left e) -> do 
            putStrLn "Error: fail in parsing the text into two propositions!"
            print e 
            putStrLn ""
            exitSuccess 
        (Right ps) -> 
            if length ps < 2 then 
                putStrLn $ printf "ERROR: need two propositions, but found %d.\n" (length ps)
            else do 
                let (a:(b:_)) = ps
                if func a b then 
                    putStrLn $ printf "TRUE: The 2nd proposition IS %s of the 1st proposition.\n" descrip
                else 
                    putStrLn $ printf "FALSE: The 2nd proposition IS NOT %s of the 1st proposition.\n" descrip

-- 读取一个文件，解析为证明过程，并判断是否正确
validateJudge path = do 
    text <- readFile path 
    case parse prove path text  of 
        (Left e) -> do 
            putStrLn "Error parsing a proof!"
            print e 
            putStrLn ""
            exitSuccess 
        (Right parsedText) -> do 
            case validate parsedText of 
                (True, _) -> do 
                    putStrLn $ printf "TRUE: The proof in \"%s\" IS valid.\n" path 
                (False, msg) -> do 
                    putStrLn $ printf "FALSE: The proof in \"%s\" IS NOT valid.\n%s\n" path msg 

syntaxError s = do 
    putStrLn $ printf "ERROR: unknwon command %s\n" s

helpInfo = putStrLn
  "Usage: logic command path\n\
  \\n\
  \logic equiv path         Check if the given two propositions are equivalent\n\
  \logic dnorm path         Check if the 2nd proposition is the principal conjunctive normal form of the 1st one\n\
  \logic cnorm path         Check if the 2nd proposition is the principal disjunctive normal form of the 1st one\n\
  \logic validate path      Check if the given proof is valid\n"
