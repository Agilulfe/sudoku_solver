from collections import deque
from copy import deepcopy
import math
import sys


def AC3(csp):
    queue = deque()
    queue.extend(list(csp.binary_constr))

    test_csp = deepcopy(csp)
    while len(queue) != 0:
        (Xi, Xj) = queue.popleft()
        if revision(test_csp, Xi, Xj):
            if len(test_csp.domain[Xi]) == 0:
                return False
            for Xk in test_csp.get_neighbors(Xi, Xj):
                queue.append((Xk, Xi))
        if Xi in test_csp.unassigned_variables:
            test_csp.assign_variable(Xi, test_csp.domain[Xi][0])
    return test_csp


def revision(test_csp, Xi, Xj):
    revised = False
    for domain_Xi in test_csp.domain[Xi]:
        legal_action = False
        for domain_Xj in test_csp.domain[Xj]:
            if domain_Xi != domain_Xj:
                legal_action = True
                break
        if not legal_action:
            test_csp.domain[Xi].remove(domain_Xi)
            revised = True
    return revised


def forward_checking(csp, variable):
    unassigned_variables = list(csp.get_unassigned_variables())
    if variable in unassigned_variables:
        unassigned_variables.remove(variable)

    for item in unassigned_variables:
        for value in list(csp.domain[item]):
            csp.assign_variable(item, value)
            if not csp.check_consistency():
                csp.domain[item].remove(value)
            if len(csp.domain[item]) == 0:
                return False
        if len(csp.domain[item]) == 1:
            csp.assign_variable(item, csp.domain[item][0])
        else:
            csp.assign_variable(item, csp.empty_tile)

    return True


def BTS(csp):
    """
    Implementation of BTS
    """
    return backtrack({}, csp)


def backtrack(board_status, csp, inference=forward_checking):

    null_variables = list(csp.get_unassigned_variables())
    for key in board_status.keys():
        if key in null_variables:
            null_variables.remove(key)

    if len(null_variables) == 0:
        return board_status

    maximum_domain = math.inf
    variable = None
    for null in null_variables:
        if len(csp.domain[null]) < maximum_domain:
            maximum_domain = len(csp.domain[null])
            variable = null

    for value in csp.domain[variable]:
        test_csp = deepcopy(csp)
        test_csp.assign_variable(variable, value)
        test_csp.unassigned_variables.remove(variable)
        if test_csp.check_consistency():
            board_status[variable] = value
            inferences = []
            if inference(test_csp, variable):
                for zero_variable in list(test_csp.get_unassigned_variables()):
                    if len(test_csp.domain[zero_variable]) == 1:
                        board_status[zero_variable] = test_csp.domain[zero_variable][0]
                        inferences.append(zero_variable)

                result = backtrack(board_status, test_csp)
                if result != False:
                    return result

            board_status.pop(variable, None)
            for zero_variable in inferences:
                board_status.pop(zero_variable, None)

    return False


class Sudoku:
    """
    This class represents a sudoku board.
    """

    def __init__(self, board):
        """
        Initiate class
        """
        self.unassigned = []
        self.board = {}
        i = 0
        for row in "ABCDEFGHI":
            for column in "123456789":
                self.board[row + column] = int(board[i])
                if self.board[row + column] == 0:
                    self.unassigned.append(row + column)
                i += 1

    def get_empty_tiles(self):
        return list(self.unassigned)

    def get_tiles(self, variable):
        return self.board[variable]

    def set_tile(self, variable, value):
        self.board[variable] = value

    def get_keys(self):
        return list(self.board.keys())


class CSP:
    """
    Class for the sudoku CSP
    """

    def __init__(self, sudoku):
        self.sudoku = sudoku
        self.variables = sudoku.get_keys()
        self.unassigned_variables = sudoku.get_empty_tiles()
        self.domain = {var: [self.sudoku.get_tiles(var)] if self.sudoku.get_tiles(
            var) != 0 else list(range(1, 10)) for var in self.variables}
        self.constraints = []
        self.empty_tile = 0

        # Row
        self.constraints.append(
            ["A1", "A2", "A3", "A4", "A5", "A6", "A7", "A8", "A9"])
        self.constraints.append(
            ["B1", "B2", "B3", "B4", "B5", "B6", "B7", "B8", "B9"])
        self.constraints.append(
            ["C1", "C2", "C3", "C4", "C5", "C6", "C7", "C8", "C9"])
        self.constraints.append(
            ["D1", "D2", "D3", "D4", "D5", "D6", "D7", "D8", "D9"])
        self.constraints.append(
            ["E1", "E2", "E3", "E4", "E5", "E6", "E7", "E8", "E9"])
        self.constraints.append(
            ["F1", "F2", "F3", "F4", "F5", "F6", "F7", "F8", "F9"])
        self.constraints.append(
            ["G1", "G2", "G3", "G4", "G5", "G6", "G7", "G8", "G9"])
        self.constraints.append(
            ["H1", "H2", "H3", "H4", "H5", "H6", "H7", "H8", "H9"])
        self.constraints.append(
            ["I1", "I2", "I3", "I4", "I5", "I6", "I7", "I8", "I9"])

        # Column
        self.constraints.append(
            ["A1", "B1", "C1", "D1", "E1", "F1", "G1", "H1", "I1"])
        self.constraints.append(
            ["A2", "B2", "C2", "D2", "E2", "F2", "G2", "H2", "I2"])
        self.constraints.append(
            ["A3", "B3", "C3", "D3", "E3", "F3", "G3", "H3", "I3"])
        self.constraints.append(
            ["A4", "B4", "C4", "D4", "E4", "F4", "G4", "H4", "I4"])
        self.constraints.append(
            ["A5", "B5", "C5", "D5", "E5", "F5", "G5", "H5", "I5"])
        self.constraints.append(
            ["A6", "B6", "C6", "D6", "E6", "F6", "G6", "H6", "I6"])
        self.constraints.append(
            ["A7", "B7", "C7", "D7", "E7", "F7", "G7", "H7", "I7"])
        self.constraints.append(
            ["A8", "B8", "C8", "D8", "E8", "F8", "G8", "H8", "I8"])
        self.constraints.append(
            ["A9", "B9", "C9", "D9", "E9", "F9", "G9", "H9", "I9"])

        # 3x3 squares
        self.constraints.append(
            ["A1", "A2", "A3", "B1", "B2", "B3", "C1", "C2", "C3"])
        self.constraints.append(
            ["D1", "D2", "D3", "E1", "E2", "E3", "F1", "F2", "F3"])
        self.constraints.append(
            ["G1", "G2", "G3", "H1", "H2", "H3", "I1", "I2", "I3"])
        self.constraints.append(
            ["A4", "A5", "A6", "B4", "B5", "B6", "C4", "C5", "C6"])
        self.constraints.append(
            ["D4", "D5", "D6", "E4", "E5", "E6", "F4", "F5", "F6"])
        self.constraints.append(
            ["G4", "G5", "G6", "H4", "H5", "H6", "I4", "I5", "I6"])
        self.constraints.append(
            ["A7", "A8", "A9", "B7", "B8", "B9", "C7", "C8", "C9"])
        self.constraints.append(
            ["D7", "D8", "D9", "E7", "E8", "E9", "F7", "F8", "F9"])
        self.constraints.append(
            ["G7", "G8", "G9", "H7", "H8", "H9", "I7", "I8", "I9"])

        self.binary_constr = []
        for tile in self.variables:
            for constraint in self.constraints:
                if tile in constraint:
                    for other_tile in constraint:
                        if other_tile != tile:
                            self.binary_constr.append((tile, other_tile))

    def get_neighbors(self, tile, restriction=None):
        neighbors = []
        for arc_relation in self.binary_constr:
            if tile == arc_relation[0]:
                if restriction is not None:
                    if restriction != arc_relation[1]:
                        neighbors.append(arc_relation[1])
                else:
                    neighbors.append(arc_relation[1])
        return neighbors

    def get_unassigned_variables(self):
        return self.unassigned_variables

    def assign_variable(self, variable, value):
        self.sudoku.set_tile(variable, value)

    def check_consistency(self):
        is_consistent = True
        for constraint in self.constraints:
            is_consistent = is_consistent and self.all_different(constraint)
        return is_consistent

    def all_different(self, variables):
        length = len(variables)
        for i in range(length - 1):
            if self.sudoku.get_tiles(variables[i]) != 0:
                for j in range(i + 1, length):
                    if self.sudoku.get_tiles(variables[j]) != 0:
                        if self.sudoku.get_tiles(variables[i]) == self.sudoku.get_tiles(variables[j]):
                            return False
        return True


def main(csp):
    """Main function"""
    with open("output.txt", "w") as output:
        solution = ""
        ac3_solution = AC3(csp)
        if ac3_solution is not False and ac3_solution.check_consistency() is True:
            for row in "ABCDEFGHI":
                for col in "123456789":
                    solution += str(ac3_solution.domain[row + col][0])

            solution += " AC3"
            output.write(solution)
            return

        solved_sudoku = BTS(csp)
        for tile in solved_sudoku:
            csp.domain[tile] = [solved_sudoku[tile]]

        for row in "ABCDEFGHI":
            for col in "123456789":
                solution += str(csp.domain[row + col][0])

        solution += " BTS"

        output.write(solution)


if __name__ == '__main__':
    if len(sys.argv) != 2:
        print('Use the correct arguments to run the program')

    else:
        board = Sudoku(sys.argv[1])
        csp = CSP(board)
        main(csp)
