module Main

main : IO ()
main = putStrLn $ show $ List.reverse (the (List Int) [])
-- main = pure ()
-- main = let x = List.reverse [1..10] in pure ()
