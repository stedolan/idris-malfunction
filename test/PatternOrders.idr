module Main

f : Maybe Integer -> Int
f x = 3
f (Just _) = 1
f Nothing = 0

main : IO ()
main = do
    putStrLn $ show $ f (Just 3)
    putStrLn $ show $ f Nothing