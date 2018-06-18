module Main

f : Int -> Bool
f n = if n `mod` 2 == 0 then True else False

factx : Int -> Lazy Int
factx 0 = 0
factx n = n + factx (n - 1)

main : IO ()
main = do
    let t = sum [0,50,50]
    -- let t = 100
    putStrLn $ show $ t
    let abc = factx $ t
    putStrLn $ show $ Force abc
    -- putStrLn $ show $ abc
    putStrLn $ show $ f abc