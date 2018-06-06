module Main

myunwords : List String -> String
myunwords [] = ""
myunwords [x] = x
myunwords (x :: xs) = x ++ " " ++ myunwords xs

myunlines : List String -> String
myunlines [] = ""
myunlines [x] = x
myunlines (x :: xs) = x ++ "\n" ++ myunlines xs

main : IO ()
main = do
    let justAList = reverse ["hello", "world"]
    putStrLn $ myunwords justAList
    putStrLn $ show $ myunwords justAList
    putStrLn $ myunlines justAList
    putStrLn $ show $ myunlines justAList
    putStrLn $ show $ if True then [1..10] else [20,9..1]
