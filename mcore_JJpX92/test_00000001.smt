(declare-fun STDIN_1 () (Array (_ BitVec 32) (_ BitVec 8)))
(declare-fun aux728 () (_ BitVec 8))(assert (= aux728 (select STDIN_1 #x00000003)))
(declare-fun aux729 () (_ BitVec 8))(assert (= aux729 (select STDIN_1 #x00000002)))
(declare-fun aux730 () (_ BitVec 8))(assert (= aux730 (select STDIN_1 #x00000001)))
(declare-fun aux731 () (_ BitVec 8))(assert (= aux731 (select STDIN_1 #x00000000)))
(declare-fun aux732 () (_ BitVec 32))(assert (= aux732 (concat aux728 aux729 aux730 aux731)))
(declare-fun aux733 () (_ BitVec 32))(assert (= aux733 (bvsub aux732 #x00000041)))
(declare-fun aux734 () Bool)(assert (= aux734 (= aux733 #x00000000)))
(declare-fun aux735 () Bool)(assert (= aux735 (bvult aux732 #x00000041)))
(declare-fun aux736 () Bool)(assert (= aux736 (= aux735 false)))
(declare-fun aux737 () Bool)(assert (= aux737 (= aux734 false)))
(declare-fun aux738 () Bool)(assert (= aux738 (and aux736 aux737)))
(declare-fun aux739 () (_ BitVec 64))(assert (= aux739 #x0000000000400642))
(declare-fun aux740 () (_ BitVec 64))(assert (= aux740 #x0000000000400621))
(declare-fun aux741 () (_ BitVec 64))(assert (= aux741 (ite aux738 aux739 aux740)))
(declare-fun aux742 () (_ BitVec 64))(assert (= aux742 #x0000000000400621))
(assert (= aux741 aux742))
