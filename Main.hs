import Func 
import Prop
import Parse
import Text.ParserCombinators.Parsec 

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