module Main

f : Int -> Bool
-- f n = if n `mod` 3 == 0 then True else False
f n = n `mod` 3 == 0

factx :  Lazy Int -> Lazy Int
factx 0 = 1
factx n = n * factx (n - 1)

main : IO ()
main = putStrLn $ show $ f $ factx (sum [1..10])
-- main = getLine >>= putStrLn
