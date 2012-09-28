#!/usr/bin/perl
# *
# *
# *      Copyright (c) 2012 Colorado State University
# *
# *      Permission is hereby granted, free of charge, to any person
# *      obtaining a copy of this software and associated documentation
# *      files (the "Software"), to deal in the Software without
# *      restriction, including without limitation the rights to use,
# *      copy, modify, merge, publish, distribute, sublicense, and/or
# *      sell copies of the Software, and to permit persons to whom
# *      the Software is furnished to do so, subject to the following
# *      conditions:
# *
# *      The above copyright notice and this permission notice shall be
# *      included in all copies or substantial portions of the Software.
# *
# *      THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
# *      EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
# *      OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
# *      NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT
# *      HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
# *      WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
# *      FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
# *      OTHER DEALINGS IN THE SOFTWARE.\
# *
# *
# *  File: bgpmon-archiver-status.pl
# *      Authors: Kaustubh Gadkari, Dan Massey, Cathie Olschanowsky
# *  Date: May 16, 2012
# *

use strict;
use warnings;
use Getopt::Long;
use BGPmon::Log;
use DateTime::Format::ISO8601;
use DateTime;
use Net::SMTP;

BEGIN{
	our $VERSION = 1.02;
};

my $prog_name = $0;

$! = 1;

# checking parameters
# warn after this many seconds with no status updates
my $status_warn_threshold = 900;
# restart after this many seconds with no status updates
my $status_restart_threshold = 1800;
# warn after this many seconds with no updates logged
my $update_warn_threshold = 270;
# restart after this many seconds with no status updates
my $update_restart_threshold = 500;

# Variables for logging
my $syslog = 0;
my $loglevel = 7;
my $logfile;

# Archiver locations
my $archiver_status;
my $data_dir;

# install locations
# location of bgpmon-archiver etc directory
my $var_dir;
if (defined($ENV{'ARCHIVER_STATE'})) {
    $var_dir = $ENV{'ARCHIVER_STATE'};
} else {
    $var_dir = '/var/run/bgpmon-archiver';
}

# Parse command line options.
my $result = GetOptions("syslog" => \$syslog,
    "loglevel=i" => \$loglevel,
    "logfile=s" => \$logfile,
    "statusfile=s" => \$archiver_status,
    "datadir=s" => \$data_dir);

# Set default location of bgpmon-archiver meta data directory
unless (defined($archiver_status)) {
    $archiver_status = "/raid2/bgpmon_archive/metadata/archiver_status.log";
}

my $ret = BGPmon::Log::log_init(log_level => $loglevel,
    logfile => $logfile,
    use_syslog => $syslog,
    prog_name => $prog_name);

# check the archiver is running and restart if not.
my $pid = check_pid();
if ($pid == -1) {
    report_error("Fatal archiver error. Unable to get PID or restart.");
    exit 1;
}

# Check status logs and return list of open files
my @files = check_status($pid, $status_warn_threshold, $status_restart_threshold);
if (scalar(@files) == 0) { # Check if files is empty
    report_error("Fatal archiver error. Unable to get archive files or restart.");
    exit 1;
}

# Check at least one the files has recent data
$ret = check_updates(@files, $update_warn_threshold, $update_restart_threshold);
if ($ret == -1) {
    report_error("Fatal archiver error. Unable to get recent updates or restart.");
    exit 1;
}

report_success();

exit 0;

# get the PID for the archiver or -1 if no PID found
sub check_pid {
    # Check if pid file exists
    my $pid_file = "$var_dir/archiver.pid";

    until (-e $pid_file) {
        restart_archiver();
    }

    my $pid = get_pid();

    # Loop through output of ps command.
    my $ret = 0;
    while (<PS_F>) {
        $_ =~ s/\s+/ /g;
        my @ps_elems = split;
        my $ps_pid = $ps_elems[0];
        if ($ps_pid == $pid) {
            $ret = $pid;
        }
    }
    close(PS_F);

    if ($ret == $pid) {
        return $ret;
    } else {
        $pid = restart_archiver();
        return $pid;
    }
}

sub get_pid {
    my $pid_file = "$var_dir/archiver.pid";
    unless (-e $pid_file) {
        return -1;
    }

    if (!open(PID_F, $pid_file)) {
        report_error("Unable to read existing PID file $pid_file.");
        return -1;
    }
    my $pid = <PID_F>;
    close(PID_F);
    return $pid;
}

# get the time since the last status message was written by the archiver
sub check_status {
    my ($pid, $warn, $restart) = @_;

    # Get last 100 lines of the log file
    if (!open(STATUS_F, "tail -n 100 $archiver_status|")) {
        report_error("Unable to read existing log file $archiver_status.");
        return undef;
    }

    my @files;
    my $log_time;

    while (<STATUS_F>) {
        chomp;
        my @line_elems = split(/\s+/);
        # Skip lines not matching the current pid.
        my @cmd_elems = split(/\[/, $line_elems[1]);
        $cmd_elems[1] =~ s/\]\://g;
        if ($cmd_elems[1] == $pid) {
            if ($line_elems[2] eq "OPENING:") {
                push(@files, $line_elems[4]);
                $log_time = $line_elems[0];
            } elsif ($line_elems[2] eq "ROLLING:") {
                undef @files;
                $log_time = $line_elems[0];
            } elsif ($line_elems[2] eq "STARTED:" or $line_elems[2] eq "CLOSING:") {
                $log_time = $line_elems[0];
            } else {
                report_error("Unable to read existing log file $archiver_status.");
                return undef;
            }
        }
    }

    # Check if log_time - curr time is within threshold
    # If out of restart threshold, restart archiver.

    my $ts = get_epoch($log_time);
    my $now = time();
    my $diff = $now - $ts;
    if ($diff > $warn && $diff < $restart) {
        report_error("No status messages logged by archiver in $diff seconds, exceeding the warning threshold");
    } elsif ($diff > $warn && $diff >= $restart) {
        report_error("No status messages logged by archiver in $diff seconds, exceeding the restart threshold. Restarting archiver.");
        restart_archiver();
    }

    return @files;
}

# get the time since the last update message was logged by the archiver
sub check_updates {
    my (@files, $warn, $restart) = @_;

    # Check if we have any files to process.
    # Return -1 if none.
    if (scalar(@files) == 0) {
        return -1;
    }

    # Read last line of each file and get time stamp of latest update.
    # The timestamps for XML files and bgpdump files are different.
    my $ts = 0;
    my $log_time;
    foreach my $file (@files) {
        # Read last line of file.
        my $line = `tail -1 $file`;

        # Get timestamp
        if ($file =~ /xml/) {
            $line =~ /<BGP_MESSAGE.*?timestamp="(\d*)/;
            $log_time = $1;
        } elsif ($file =~ /bgpdump/) {
            my @line_elems = split(/\|/, $line);
            $log_time = $line_elems[0];
        }
        if ($ts < $log_time) {
            $ts = $log_time;
        }
    }

    # Check if the time stamp is recent enough.
    my $now = time();
    my $diff = $now - $ts;
    if ($diff > $warn && $diff < $restart) {
        report_error("No status messages logged by archiver in $diff seconds, exceeding the warning threshold");
    } elsif ($diff > $warn && $diff >= $restart) {
        report_error("No status messages logged by archiver in $diff seconds, exceeding the restart threshold\n
            Restarting archiver.");
        $pid = restart_archiver();
    }
    return 0;
}

# restart the archiver
sub restart_archiver {
    report_warning("Attempting to restart bgpmon-archiver");

    # if this fails, how long do I wait to try again
    my $try_again_time = 2;
    # if this fails, increase delay time by multiply by delay factor
    my $delay_factor = 2;

    # once we restart the archiver, how long do we expect it to take until it starts.
    my $timeout = 180;   # if the archiver isn't getting updates within 3 minutes, it didn't start
    my $time = 0;    # how much time has elapsed since the archiver was relaunched
    my $check_delay = 3;   # check every 3 seconds to see how the archiver is doing
    my $elapsed_time = 0;  # how much time has elapsed since we launched the startup script?

    # continue trying until we get the archiver started
    while (1) {
        `sudo /etc/init.d/bgpmon-archiver start`;
        if ($?) {
        # if the startup script failed, no need to wait and see if successfully started.   just set time out and that will drop us to end of loop.
            $time = $timeout;
        } else {
            # we launched the startup script,  now we need to run through all the checks before the timeout...
            $time = 0;
            while ($time < $timeout && get_pid() == -1) {
                # didn't see a valid PID yet so sleep and check again
                sleep($check_delay);
                $elapsed_time += $check_delay;
            }
            # we either have a valid PID or have timed out,    now try for status message
            while ($time < $timeout && check_status() == undef) {
                # didn't see the necessary status messages yet so sleep and check again
                sleep($check_delay);
                $elapsed_time += $check_delay;
            }
            # we either have a valid status message or have time out,   now look for log messages
            while ($time < $timeout && check_log() == -1) {
                # didn't see the log messages yet so sleep and then check again
                sleep($check_delay);
                $elapsed_time += $check_delay;
            }
            # if we didn't time out,  it successfully restarted so log that fact and quit
            if ($time < $timeout) {
                report_success("Successfully restarted bgpmon_archiver");
                exit 0;
            # otherwise it didn't successfully restart,  adjust the delay until trying again and start over
            } else {
                $try_again_time = $try_again_time * $delay_factor;
                report_warning("Failed to restart bgpmon_archiver, will try again in $try_again_time seconds");
                sleep($try_again_time);
            }
            # if we reach here,   the program has timed out and the delayed for some time.   go back to start and try another restart
        }
    }
    # this is never reached....   the loop either continues to retry forever or the program exits if the restart succeeded
    return 0;
}

# report an error
sub report_error {
    my $msg = shift;
    my $subject = "bgpmon-archiver error";
    BGPmon::Log::log_err($msg);
    my $ret = send_mail($msg, $subject);
    if ($ret == 0) {
        return 0;
    } else {
        BGPmon::Log::log_err("Error sending email.");
        return -1;
    }
}

# report a warning
sub report_warning {
    my $msg = shift;
    my $subject = "bgpmon-archiver warning";
    BGPmon::Log::log_warn($msg);
    my $ret = send_mail($msg, $subject);
    if ($ret == 0) {
        return 0;
    } else {
        BGPmon::Log::log_err("Error sending email.");
        return -1;
    }
}

# report success
sub report_success {
    my $msg = shift;
    my $subject = "bgpmon-archiver success";
    BGPmon::Log::log_info($msg);
    my $ret = send_mail($msg, $subject);
    if ($ret == 0) {
        return 0;
    } else {
        BGPmon::Log::log_err("Error sending email.");
        return -1;
    }
    send_mail($msg, $subject);
    return 0;
}

# Send email
sub send_mail {
    my ($msg, $subject) = @_;
#    my $smtp = Net::SMTP->new(
#            Host => 'alpha.netsec.colostate.edu',
#            Hello => 'netsec.colostate.edu',);
#    $smtp->mail($ENV{USER});
#    $smtp->to('kaustubh@cs.colostate.edu');
#
#    $smtp->data();
#    $smtp->datasend("To: kaustubh\@cs.colostate.edu\n");
#    $smtp->datasend("\n");
#    $smtp->datasend($msg);
#    $smtp->dataend();
#    $smtp->quit();

    return 0;
}

# Convert time from log to Unix epoch.
sub get_epoch {
    my $log_time = shift;
    my @log_time_elems = split (/\(/, $log_time);
    my $dt = DateTime::Format::ISO8601->parse_datetime($log_time_elems[0]);
    return $dt->epoch;
}
