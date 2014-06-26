(declare-datatypes () ((Record (mkRecord (m Int)))))
(assert (= (m (mkRecord 4)) 4))
(check-sat)