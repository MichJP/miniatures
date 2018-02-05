import System.Environment (getArgs)
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
getSeq n input = reverse . snd $ foldl getNextState (input, []) [0..n - 1]

main = do
    args <- getArgs
    let n = if length args > 0 then read (args !! 0) :: Int else 100
    let maxN = if length args > 1 then read (args !! 1) else -1
    let input = if maxN < 0 then [1..] else cycle [1..maxN]
    mapM_ (putStrLn . show) $ getSeq n input

