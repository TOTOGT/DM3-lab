"""Fixtures cover false-positive/false-negative risks in unattended axiom gates."""

import unittest

from check_axioms import check_reports


class AxiomGateFixtures(unittest.TestCase):
    def test_adjacent_standard_report_cannot_hide_first_external_axiom(self):
        log = "'ED.first' depends on axioms: [External.RP]\n" \
              "'ED.second' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
        result = check_reports(log, ["ED.first", "ED.second"])
        self.assertFalse(result["ok"])
        self.assertEqual(result["targets"][0]["axioms"], ["External.RP"])
        self.assertTrue(result["targets"][1]["ok"])

    def test_wrapped_list_is_one_report(self):
        log = "'ED.wrapped' depends on axioms:\n [propext,\n Classical.choice,\n Quot.sound]\n"
        self.assertTrue(check_reports(log, ["ED.wrapped"])["ok"])

    def test_missing_report_fails_even_when_neighbor_is_allowed(self):
        result = check_reports("'ED.other' depends on axioms: [propext]\n", ["ED.missing"])
        self.assertFalse(result["ok"])
        self.assertIn("missing", result["targets"][0]["error"])

    def test_sorry_ax_fails(self):
        result = check_reports("'ED.bad' depends on axioms: [propext, sorryAx]\n", ["ED.bad"])
        self.assertFalse(result["ok"])
        self.assertIn("sorryAx", result["targets"][0]["error"])

    def test_native_decide_axiom_fails_standard_allowlist(self):
        result = check_reports("'ED.bad' depends on axioms: [Lean.ofReduceBool]\n", ["ED.bad"])
        self.assertFalse(result["ok"])

    def test_duplicate_report_fails(self):
        result = check_reports("'ED.dup' depends on axioms: [propext]\n" * 2, ["ED.dup"])
        self.assertFalse(result["ok"])
        self.assertIn("duplicate", result["targets"][0]["error"])

    def test_declaration_names_are_exact_not_regexes(self):
        result = check_reports("'EDXtarget' depends on axioms: [propext]\n", ["ED.target"])
        self.assertFalse(result["ok"])

    def test_unterminated_list_cannot_borrow_neighbors_bracket(self):
        log = "'ED.first' depends on axioms: [propext\n" \
              "'ED.second' depends on axioms: [Quot.sound]\n"
        result = check_reports(log, ["ED.first", "ED.second"])
        self.assertFalse(result["ok"])
        self.assertIn("unterminated", result["targets"][0]["error"])
        self.assertTrue(result["targets"][1]["ok"])

    def test_no_axioms_report_is_valid(self):
        self.assertTrue(check_reports("'ED.pure' does not depend on any axioms\n", ["ED.pure"])["ok"])

    def test_nonreport_text_does_not_count(self):
        result = check_reports("warning: 'ED.fake' depends on axioms: [propext]\n", ["ED.fake"])
        self.assertFalse(result["ok"])

    def test_empty_entry_fails(self):
        result = check_reports("'ED.bad' depends on axioms: [propext,]\n", ["ED.bad"])
        self.assertFalse(result["ok"])


if __name__ == "__main__":
    unittest.main()
