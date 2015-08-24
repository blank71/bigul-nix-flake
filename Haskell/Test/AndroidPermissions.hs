import Lang.MonadBiGULError
import Lang.AST
import Lang.Interpreter
import Control.Monad
import Data.Char
import System.IO
import System.Process

type ApiCalls     = [SCall]
type SCall        = (SPermissions, (File, (Line, (Protected, Deleted))))
type File         = String
type Line         = Int
type Deleted      = Bool
type Name         = String
type SPermissions = [SPermission]
type SPermission  = (Name, [ApiVersion])
type Protected    = String
type ApiVersion   = String

type Calls        = [VCall]
type VCall        = (File, (Line, VPermissions))
type VPermissions = [VPermission]
type VPermission  = Name

t :: MonadError' e m => ApiVersion -> BiGUL m ApiCalls Calls
t ver = Align (\(ps, (f, (l, (ptd, del)))) -> return (not del))
              (\(_, (f, (l, _))) (f', (l', _)) -> return (f == f' && l == l'))
              (Rearr (RVar `RProd` (RVar `RProd` RVar))
                       (EDir (DRight (DRight DVar)) `EProd`
                       (EDir (DLeft DVar) `EProd`
                       (EDir (DRight (DLeft DVar)) `EProd`
                       (EConst () `EProd` EConst ()))))
                     (Update (UVar (Align (\(_, vers) -> return (ver `elem` vers))
                                          (\_ _ -> return True)
                                          (Rearr RVar (EDir DVar `EProd` EConst ())
                                                 (Update (UVar Replace `UProd` UVar Skip)))
                                          (\_ -> return ("", [ver]))
                                          (\_ -> return Nothing)) `UProd`
                             (UVar Replace `UProd`
                             (UVar Replace `UProd`
                             (UVar Skip `UProd` UVar Skip))))))
              (\_ -> return ([], ("", (0, ("", False)))))
              (\(ps, (f, (l, (ptd, del)))) -> return (Just (ps, (f, (l, (ptd, True))))))


s :: ApiCalls
s = [([("android.permission.INTERNET", ["4.0", "4.1", "4.1.1"])],
         ("./smali/b.java", (24, ("java/net/URL;->openConnection", False)))),
     ([("android.permission.INTERNET", ["4.1", "4.1.1"])],
         ("./smali/b.java", (576, ("java/net/HttpURLConnection;->connect", False)))),
     ([("android.permission.INTERNET", ["4.0"])],
         ("./smali/c.java", (9, ("", False)))),
     ([("android.permission.INTERNET", ["4.0", "4.1", "4.1.1"]),
       ("android.permission.WAKE_LOCK", ["4.0", "4.1", "4.1.1"])],
         ("./smali/com/appmk/book/main/FlipBookActivity.java", (373, ("java/net/URL;->openConnection", False))))]

v :: Calls
v = [("./smali/b.java",(24,["android.permission.INTERNET"])),
     ("./smali/b.java",(576,["android.permission.INTERNET"])),
     ("./smali/c.java",(9,[])),
     ("./smali/com/appmk/book/main/FlipBookActivity.java",(373,["android.permission.INTERNET","android.permission.WAKE_LOCK"]))]

v' :: Calls
v' = [("./smali/b.java",(24,["android.permission.INTERNET"])),
      ("./smali/b.java",(576,["android.permission.INTERNET"])),
      ("./smali/com/appmk/book/main/FlipBookActivity.java",(373,["android.permission.INTERNET","android.permission.WAKE_LOCK"])),
      ("./smali/d.java", (45, ["android.permission.WIFI"]))]



--type ApiCalls     = [SCall]
--type SCall        = (SPermissions, (File, (Line, (Protected, Deleted))))
--type File         = String
--type Line         = Int
--type Deleted      = Bool
--type Name         = String
--type SPermissions = [SPermission]
--type SPermission  = (Name, [ApiVersion])
--type Protected    = String
--type ApiVersion   = String
--
--type Calls        = [VCall]
--type VCall        = (File, (Line, VPermissions))
--type VPermissions = [VPermission]
--type VPermission  = Name

pXML :: ApiCalls -> String
pXML = element "apicalls" . concat . map (\(ps, (f, (l, (ptd, del)))) -> element "permissions" (concat (map (\(n, vers) -> element "name" n ++ concat (map (element "apiversion") vers)) ps)) ++ element "file" f ++ element "line" (show l) ++ element "protected" ptd ++ element "deleted" (map toLower (show del)))

element :: String -> String -> String
element e = (("<" ++ e ++ ">") ++) . (++ ("</" ++ e ++ ">"))

pVXML :: Calls -> String
pVXML = element "calls" . concat . map (\(f,(l, ps)) -> element "call" (element "file" f ++ element "line" (show l) ++ element "permissions" (concat ( map (element "permission" . element "name") ps ))))


writeXML :: String -> String -> IO ()
writeXML fname str = readProcess "xmllint" ["--format", "-"] str >>= writeFile fname
