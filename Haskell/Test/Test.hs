import Lang.AST
import Lang.Interpreter

s = [SBook "Real World Haskell is Not GOOD!" ["zantao"] 30.0 2015]
v = [VBook "Real World Haskell is Not GOOD!" 10.0, VBook "Learn You Haskell is GOOD!"  20.0]



putBook :: Either ErrorInfo String
putBook = catchBind (put bookstore s v) (\s' -> Right (show s')) (\e -> Left e)

getBook = catchBind (get bookstore s) (\v -> Right (show v)) (\e -> Left e)
