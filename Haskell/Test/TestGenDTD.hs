import BiFlux.DTD.GenHaskellDTD

genbooks = genHaskellDTD "Test/test/bookstore/books.dtd" "Test/test/bookstore/Books.hs"
genbookstore = genHaskellDTD "Test/test/bookstore/bookstore.dtd" "Test/test/bookstore/Bookstore.hs"
