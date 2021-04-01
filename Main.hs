import Func 
import Prop
import Parse
import Text.ParserCombinators.Parsec 
import System.Environment
import System.Exit
import Text.Printf

testDisjunc = do 
    let s1 = "(~(A->B)) /\\ ((~B) <-> C) \n"
    let s2 = "~B /\\ A /\\ C "
    case parse (many prop) "(stdin)" (s1++s2) of
        Left e -> do putStrLn "Error parsing input:"
                     print e 
        Right [p1, p2] -> do print p1
                             print p2
                             print $ disjunctiveNormValidate p1 p2

testConjunc = do 
    let s1 = "(~(A->B)) /\\ ((~B) <-> C) \n"
    let s2 = "((~A \\/ (~B \\/ ~C)) /\\ ((~A \\/ (~B \\/ C)) /\\ ((~A \\/ (B \\/ C)) /\\ ((A \\/ (~B \\/ ~C)) /\\ ((A \\/ (~B \\/ C)) /\\ ((A \\/ (B \\/ ~C)) /\\ (A \\/ (B \\/ C))))))))"
    case parse (many prop) "(stdin)" (s1++s2) of
        Left e -> do putStrLn "Error parsing input:"
                     print e 
        Right [p1, p2] -> do print p1
                             print p2
                             print $ conjunctiveNormValidate p1 p2

testProveParse = do 
    let fileName = "test_file/1.txt"
    str <- readFile fileName
    case parse prove fileName str of
        Left e -> do putStrLn "Error parsing input:"
                     print e 
        Right p -> do print p

testProveValidate = do 
    let fileName = "test_file/1.txt"
    str <- readFile fileName
    case parse prove fileName str of
        Left e -> do putStrLn "Error parsing input:"
                     print e 
        Right p -> do print p
                      print $ validate p


main = do 
    args <- getArgs
    if null args then 
        putStrLn "ERROR: found no argument."
    else if (head args /= "help") && (length args < 2) then 
        putStrLn $ printf "ERROR: need 2 arguments, but found %d." (length args)
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
    putStrLn "Please input the first proposition:\n" 
    text <- readFile path 
    case parse (many prop) path text of 
        (Left e) -> do 
            putStrLn "Error: fail in parsing the text into two propositions!\n"
            print e 
            exitSuccess 
        (Right ps) -> 
            if length ps < 2 then 
                putStrLn $ printf "ERROR: need two propositions, but found %d." (length ps)
            else do 
                let (a:(b:_)) = ps
                if isEquiv a b then 
                    putStrLn "True: The given proposition IS equivalent."
                else 
                    putStrLn "FALSE: The given proposition IS NOT equivalent."

-- 读取两个命题，判断第二个是不是第一个的主析取（合取）范式
normJudge func descrip path = do 
    putStrLn "Please input the first proposition:\n" 
    text <- readFile path 
    case parse (many prop) path text of 
        (Left e) -> do 
            putStrLn "Error: fail in parsing the text into two propositions!\n"
            print e 
            exitSuccess 
        (Right ps) -> 
            if length ps < 2 then 
                putStrLn $ printf "ERROR: need two propositions, but found %d." (length ps)
            else do 
                let (a:(b:_)) = ps
                if func a b then 
                    putStrLn $ printf "TRUE: The 2nd proposition IS %s of the 1st proposition." descrip
                else 
                    putStrLn $ printf "FALSE: The 2nd proposition IS NOT %s of the 1st proposition." descrip

-- 读取一个文件，解析为证明过程，并判断是否正确
validateJudge path = do 
    text <- readFile path 
    case parse prove path text  of 
        (Left e) -> do 
            putStrLn "Error parsing a proof!\n"
            print e 
            exitSuccess 
        (Right parsedText) -> do 
            case validate parsedText of 
                (True, _) -> do 
                    putStrLn $ printf "TRUE: The proof in \"%s\" IS valid." path 
                (False, msg) -> do 
                    putStrLn $ printf "FALSE: The proof in \"%s\" IS NOT valid.\n%s" path msg 

syntaxError s = do 
    putStrLn $ printf "ERROR: unknwon command %s" s

helpInfo = putStrLn
  "Usage: logic command path\n\
  \\n\
  \logic equiv path         Check if the given two propositions are equivalent\n\
  \logic dnorm path         Check if the 2nd proposition is the principal conjunctive normal form of the 1st one\n\
  \logic cnorm path         Check if the 2nd proposition is the principal disjunctive normal form of the 1st one\n\
  \logic validate path      Check if the given proof is valid\n"
