# -*- coding: utf-8 -*-

# SPDX-License-Identifier: MIT
# Copyright © 2021 André Santos

###############################################################################
# Imports
###############################################################################

from __future__ import unicode_literals
from builtins import object, range
import os
from subprocess import check_output, Popen, PIPE, STDOUT

import rospy


###############################################################################
# Test Runner
###############################################################################

class TestRunner(object):
    def __init__(self, iface, config):
        self.iface = iface
        self.config = config
        self._devnull = None
        self._roscore = None

    def start_roscore(self):
        self.iface.log_debug("Starting roscore.")
        if self._devnull is None:
            self._devnull = open(os.devnull, "wb")
        if self._roscore is None:
            self._roscore = Popen(["roscore"],
                stdout=self._devnull, stderr=STDOUT)
        while rospy.is_shutdown():
            rospy.sleep(1.0)
        self.iface.log_debug("Done; roscore is now running.")

    def shutdown_roscore(self):
        self.iface.log_debug("Shutting down roscore.")
        if self._roscore is not None:
            self._roscore.terminate()
            t = 10.0
            while t > 0.0 and self._roscore.poll() is None:
                rospy.sleep(1.0)
                t -= 1.0
            if self._roscore.poll() is None:
                self.iface.log_debug("Escalating to SIGKILL.")
                self._roscore.kill()
                t = 10.0
                while t > 0.0 and self._roscore.poll() is None:
                    rospy.sleep(1.0)
                    t -= 1.0
        if self._devnull is not None:
            self._devnull.close()
        if self._roscore.poll() is None:
            self.iface.log_error("Failed to shut down roscore.")
        else:
            self.iface.log_debug("Done; roscore is now shut down.")
        self._roscore = None
        self._devnull = None

    def run_tests(self, test_files):
        self.iface.log_debug("Running generated test scripts.")
        cmd = ["python", ""]
        for filename in test_files:
            cmd[-1] = filename
            self.iface.log_debug("Running test script at: "
                + os.path.abspath(filename))
            output = check_output(cmd, stderr=STDOUT)
            output = output.decode("utf-8")
            self.iface.log_debug("Done. Full output:\n" + output)
            self.iface.log_debug("Parsing test output.")
            output = output.splitlines()
            details, resources = self._parse_counterexample(output)
            if details:
                self.iface.log_debug(
                    "FAILED.\nDetails: {}\nResources:{}".format(
                        details, resources))
                self.iface.report_runtime_violation(
                    "pbtest", details, resources=resources)
            else:
                self.iface.log_debug("OK.")

    _ISSUE_HTML = (
        "<p>The following property is false.</p>"
        '<p><span class="code">{hplp}</span></p>'
        "<p><b>Counterexample:</b></p>"
        "{ce}"
    )

    _CE_OTHER_HTML = "<p>{}</p>"
    _CE_HTML = "<ol>{}</ol>"
    _CE_HTML_ITEM = (
        "<li>"
        '<i class="fa fa-arrow-alt-circle-{updown}"></i> '
        "{text}"
        "<br>"
        '<span class="code">{msg}</span>'
        "</li>"
    )
    _CE_ENTRY_MARKERS = (">> ", "<< ")

    def _parse_counterexample(self, output):
        ce_lines = []
        # --- get the output segment relative to the counterexample ---
        for i in range(len(output)):
            if output[i] == "### BEGIN COUNTEREXAMPLE ###":
                for j in range(i + 1, len(output)):
                    if output[j] == "### END COUNTEREXAMPLE ###":
                        break
                    ce_lines.append(output[j])
                break
        else:
            return (None, None) # No counterexample. All tests passed.
        # --- get the falsified property ---
        hplp = "(unknown)"
        for line in output:
            if line.startswith("AssertionError:"):
                hplp = line[16:]
        resources = set()
        # --- handle counterexamples without messages ---
        if not ce_lines or ce_lines[0].startswith("No messages"):
            ce_text = self._CE_OTHER_HTML.format(ce_lines[0])
            details = self._ISSUE_HTML.format(hplp=hplp, ce=ce_text)
            return (details, resources)
        # --- parse individual messages of the counterexample ---
        ce_items = []
        for i in range(len(ce_lines)):
            line = ce_lines[i]
            if line.startswith(self._CE_ENTRY_MARKERS):
                item = self._CE_HTML_ITEM.format(
                    updown=("up" if line.startswith(">") else "down"),
                    text=line[3:],
                    msg=self._output_msg_to_html(ce_lines, i + 1)
                )
                ce_items.append(item)
                r = self._resource_from_entry(line)
                if r is not None:
                    resources.add(r)
            else:
                pass # skip msg output
        ce_text = self._CE_HTML.format("".join(ce_items))
        details = self._ISSUE_HTML.format(hplp=hplp, ce=ce_text)
        return (details, resources)

    _STRING_MARKERS = ("b'", "u'", "'")

    def _output_msg_to_html(self, ce_lines, start):
        if ce_lines[start].startswith("("):
            return ce_lines[start]
        msg_lines = []
        for i in range(start, len(ce_lines)):
            if ce_lines[i].startswith(self._CE_ENTRY_MARKERS):
                break
            msg_lines.append(ce_lines[i])
        if msg_lines and msg_lines[0].startswith(self._STRING_MARKERS):
            msg_lines[0] = msg_lines[0].split("'", 1)[-1]
            if msg_lines[-1].endswith("'"):
                msg_lines[-1] = msg_lines[-1][:-1]
        msg = "<br>".join(msg_lines)
        return msg.replace(" ", "&nbsp;")

    def _resource_from_entry(self, entry):
        # receives a line in the form
        #   ">> @{time}ms sent {spam/witness} on {topic}"
        # or
        #   "<< @{time}ms received on {topic}"
        rosname = entry.rsplit("on ", 1)[-1]
        for topic in self.config.topics.enabled:
            if topic.rosname.full == rosname:
                return topic
            if topic.rosname.own == rosname:
                return topic
        for topic in self.config.topics.conditional:
            if topic.disabled:
                continue
            if topic.rosname.full == rosname:
                return topic
            if topic.rosname.own == rosname:
                return topic
        return None
