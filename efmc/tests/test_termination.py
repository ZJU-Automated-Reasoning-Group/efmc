# coding: utf-8
import logging
import z3

from efmc.tests import TestCase, main
from efmc.engines.termination.termination import verify_termination


class TestPTermination(TestCase):

    def test_bool_program(self):
        return
        # verify_termination("efmc/test.smt2", strategy="lex")


if __name__ == '__main__':
    logging.basicConfig(level=logging.DEBUG)
    main()
