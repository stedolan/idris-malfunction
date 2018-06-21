module Main

f : List Integer -> Bool
f [1, 1124000727777607680000] = True
f [1124000727777607680000] = True
f [1124000727777607680001] = True
f [2] = True
f [] = True
f _ = False

ff : Integer -> Maybe Integer
ff 1124000727777607680000 = Just 2003
ff 123123213123123 = Nothing
ff _ = Just 0

main : IO ()
main = do
     putStrLn $ show $ f  [1, product [1..22]]
     putStrLn $ show $ f  [product [1..22] + 1]
     putStrLn $ show $ f  [product [1..22]]
     putStrLn $ show $ f (2 :: [])
     putStrLn $ show $ f [2, 3, 4]
     putStrLn $ show $ f []
     putStrLn $ show $ ff 1124000727777607680000
     putStrLn $ show $ ff 123123213123123
     putStrLn $ show $ ff (-3)


     

