"""
FIXME: not implemented yet!
"""
import re


class CToSyGuSConverter:
    def __init__(self):
        self.variables = []
        self.assumptions = []
        self.loop_condition = ""
        self.loop_body = []
        self.assertion = ""


# Example usage
def main():
    c_program = """
    int x;
    int y;

    assume(x == -50);

    while(x < 0){
        x = x + y;
        y = y + 1;
    }

    assert(y > 0);
    """

    converter = CToSyGuSConverter()
    sygus_output = converter.convert(c_program)
    print(sygus_output)


if __name__ == "__main__":
    main()
