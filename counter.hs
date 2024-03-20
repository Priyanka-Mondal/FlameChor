--import Data.IORef
        
type Counter = Int -> IO Int 
        
makeCounter :: IO Counter
makeCounter = do
    r <- newIORef 0
    return (\i -> do modifyIORef r (+i)
                     readIORef r)

testCounter :: Counter -> IO ()
testCounter counter = do
    b <- counter 1
    print b

inc :: Counter -> Int 
inc c = do  
    	ne <- c 1
        return 2*ne
main = do
    counter <- makeCounter
    testCounter counter
    testCounter counter
