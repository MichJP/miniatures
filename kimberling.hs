import Control.Monad

interleave :: [a] -> [a] -> [a]
interleave [] rs = rs
interleave ls [] = reverse ls
interleave (l:ls) (r:rs) = r:l:interleave ls rs

getNextState :: ([a], [a]) -> Int -> ([a], [a])
getNextState (buffer, acc) i = (buffer', acc')
  where (left, xs) = splitAt i buffer
        item = head xs
        right = tail xs
        buffer' = interleave (reverse left) right
        acc' = item:acc


getSeq :: Int -> [a] -> [a]
getSeq n input = reverse . snd $ foldl getNextState (input, []) [0..n]

main = mapM_ (putStrLn . show) $ getSeq 100 input
  where input = cycle [1, 2, 3, 4, 5]

