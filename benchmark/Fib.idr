myfib : Integer -> Integer
myfib 0 = 1
myfib 1 = 1
myfib n = myfib (n - 1) + myfib (n - 2)

main : IO ()
main = putStrLn $ show $ myfib 40
