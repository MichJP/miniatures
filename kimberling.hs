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

getSeq :: Int -> [Int]
getSeq n = reverse . snd $ foldl getNextState ([1..], []) [0..n]

