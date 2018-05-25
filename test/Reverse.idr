module Main

main : IO ()
-- main = putStrLn $ show $ List.reverse (the (List Int) [])
main = do
    let ioanluca = reverse [1,2,3]
    putStrLn $ show $ ioanluca
-- main = pure ()
-- main = let x = List.reverse [1..10] in pure ()
