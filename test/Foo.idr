module Main

main : IO ()
main = 
   let s = [1..] in putStrLn $ show $ take 100 s
