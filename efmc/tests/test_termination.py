# coding: utf-8
import logging

from efmc.tests import TestCase, main


class TestPTermination(TestCase):

    def test_bool_program(self):
        return
        # verify_termination("efmc/test.smt2", strategy="lex")


if __name__ == '__main__':
    logging.basicConfig(level=logging.DEBUG)
    main()
