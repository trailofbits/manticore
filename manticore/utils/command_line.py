"""
NOTE: Most of the code here is compatible/taken from Slither project ( https://github.com/trailofbits/slither ).
to be compatible with it.
"""
from prettytable import PrettyTable

from ..ethereum.detectors import DetectorClassification

classification_txt = {
    DetectorClassification.INFORMATIONAL: "Informational",
    DetectorClassification.LOW: "Low",
    DetectorClassification.MEDIUM: "Medium",
    DetectorClassification.HIGH: "High",
}


def output_detectors(detector_classes):
    """
    Copied from
    https://github.com/trailofbits/slither/blob/563d5118298e4cae7f0ea5f2a531f0dcdcebd64d/slither/utils/command_line.py
    """
    detectors_list = []

    for detector in detector_classes:
        argument = detector.ARGUMENT
        help_info = detector.HELP
        impact = detector.IMPACT
        confidence = classification_txt[detector.CONFIDENCE]
        detectors_list.append((argument, help_info, impact, confidence))

    table = PrettyTable(["Num", "Check", "What it Detects", "Impact", "Confidence"])

    # Sort by impact, confidence, and name
    detectors_list = sorted(
        detectors_list, key=lambda element: (element[2], element[3], element[0])
    )
    idx = 1
    for (argument, help_info, impact, confidence) in detectors_list:
        table.add_row([idx, argument, help_info, classification_txt[impact], confidence])
        idx = idx + 1

    print(table)
