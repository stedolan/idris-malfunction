module Main

main : IO ()
main = do putStrLn $ show $ map (\x => x + 1) $ Just 3
          putStrLn $ show $ map (*3) $ reverse [1..10]