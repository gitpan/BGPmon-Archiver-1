#!/usr/bin/perl
$VERSION = 1.01;
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
# *      OTHER DEALINGS IN THE SOFTWARE.
# *
# *
# *  File: bgpmon_archiver.pl
# *  Authors: Kaustubh Gadkari, Dan Massey, Cathie Olschanowsky
# *  Date: Aug 24, 2012
# *

use strict;
use warnings;
use Getopt::Long;
use POSIX qw(strftime setsid getpid);
use File::Path qw/make_path/;
use BGPmon::Log ':all';
use BGPmon::Fetch qw(connect_bgpdata read_xml_message close_connection get_error_code get_error_message);
use BGPmon::Translator::XFB2BGPdump qw(translate_message get_error_code get_error_message);
use BGPmon::Translator::XFB2PerlHash::Simple qw(init get_timestamp get_error_code get_error_message get_error_msg get_xml_message_type get_peering);
use Cwd;
use Fcntl 'SEEK_END';

# SAFI of -255 implies XML message.
use constant XML_SAFI => -255;

#---- Default settings ----
# These settings are used if the user does not specify the values
# via either the config file or the command line.
use constant DEFAULT_UPDATE_PORT => 50001;
use constant DEFAULT_RIB_PORT => 50002;
use constant DEFAULT_SERVER => 'livebgp.netsec.colostate.edu';
use constant DEFAULT_LOG_LEVEL => BGPmon::Log::LOG_WARNING;
use constant DEFAULT_RETRY_INTERVAL => 30;
use constant DEFAULT_ROLL_INTERVAL => 900;

$| = 1;

#---- Get program name. ----
my $prog_name = $0;

#---- Get pid. ----
my $pid = getpid();

#---- Get current working directory. ----
my $cwd = getcwd();

#---- Global variables. ----
my $debug = 0;

##--- File handles hash, indexed by file name.
my %file_fhs;

##--- Current output directory. ---
my $curr_dir_path = "";

##--- Variables for logging ---
my $log_level;
my $use_syslog;
my $log_file;

#---- BGPmon variables ----
my $server;
my $port;

#---- Archiver config variables ----
my $roll_interval;
my $ribs;
my $out_dir;
my $peer_out_dir;
my $config_file;
my $archive_bgpdump;
my $status_file;
my $status_fh;
my $use_stdout_for_status = 0;
my $is_daemon;
my $retry_interval;
my $no_pid;

#---- Hash to store config options. ----
my %config;

#---- Archiver status variables. ----
my $messages_read = 0;
my $messages_archived = 0;
my $curr_messages_archived = 0;

#---- BEGIN main ----

# Set signal handlers.
$SIG{INT} = $SIG{TERM} = $SIG{KILL} = $SIG{HUP} = \&archiver_exit;
$SIG{PIPE} = 'ignore';

#---- Get the command line options. ----
my $result = GetOptions("server=s" => \$server,
                           "port=s" => \$port,
                           "daemonize" => \$is_daemon,
                           "outdir=s" => \$out_dir,
                           "peeroutdir=s" => \$peer_out_dir,
                           "ribs" => \$ribs,
                           "bgpdump" => \$archive_bgpdump,
                           "debug" => \$debug,
                           "rolltime=i" => \$roll_interval,
                           "config=s" => \$config_file,
                           "statusfile=s" => \$status_file,
                           "syslog" => \$use_syslog,
                           "loglevel=i" => \$log_level,
                           "logfile=s" => \$log_file,
                           "nopid" => \$no_pid,
                           "retryinterval=i" => \$retry_interval,);
die "Usage: bgpmon-archiver.pl [-debug] [-daemonize]
        [-config /path/to/configfile]
        [-statusfile /path/to/statusfile]
        [-nopid do not write pid file]
        [-server A.B.C.D] [-port port] [-rolltime roll interval (in sec.)]
        [-outdir /path/to/directory]
        [-peeroutdir /path/to/peersdirectory]
        [-ribs archive ribs (off by default)]
        [-bgpdump convert XML messages to BGPdump format messages]
        [-sylog use syslog to log messages]
        [-loglevel logging level]
        [-retryinterval number of seconds to wait between reconnect attempts]
        [-logfile /path/to/logfile]" unless $result;

#---- Set the config file location. ----
if (defined($config_file)) {
    $config{conf_file} = $config_file;
} else {
    $config{conf_file} = '/usr/local/etc/bgpmon-archiver.conf';
}

#---- Parse the config file. ----
if (parse_config_file($config{conf_file}) == -1) {
    print STDERR "Could not read config file $config{conf_file}.\n";
    exit 1;
}

#---- Set defaults. ----
# Connect to the live BGP stream by default.
if (defined($server)) {
    $config{server} = $server;
} elsif (!defined($config{server})) {
    $config{server} = DEFAULT_SERVER;
}

# Connect to UPDATEs port by default.
if (defined($port)) {
    $config{port} = $port;
} elsif (!defined($config{port})) {
    $config{port} = DEFAULT_UPDATE_PORT;
}

# The output files roll after 15 minutes by default.
if (defined($roll_interval)) {
    $config{roll_interval} = $roll_interval;
} elsif (!defined($config{roll_interval})) {
    $config{roll_interval} = DEFAULT_ROLL_INTERVAL;
}

# Set the retry interval to 30s by default
unless (defined($retry_interval) && $retry_interval > 0) {
    $retry_interval = DEFAULT_RETRY_INTERVAL;
}

# The default logging level is LOG_WARNING.
if (defined($log_level)) {
    $config{log_level} = $log_level;
} elsif (!defined($config{log_level})) {
    $config{log_level} = DEFAULT_LOG_LEVEL;
}

# Do not use syslog by default.
if (defined($use_syslog)) {
    $config{use_syslog} = $use_syslog;
} elsif (!defined($config{use_syslog})) {
    $config{use_syslog} = 0;
}

# Set log file, if specified.
if (defined($log_file)) {
    $config{log_file} = $log_file;
} elsif (!defined($config{log_file})) {
    $config{log_file} = undef;
}

# Unless specified, do not archive bgpdump format messages.
if (defined($archive_bgpdump)) {
    $config{archive_bgpdump} = $archive_bgpdump;
} elsif (!defined($config{archive_bgpdump})) {
    $config{archive_bgpdump} = 0;
}

# Set default output directory. If not specified at cmd line
# or config file, set to ./archives/date.
if (defined($out_dir)) {
    $config{out_dir} = $out_dir;
} elsif (!defined($config{out_dir})) {
    $config{out_dir} = "$cwd/archives/date";
}

# Set default output directory for per peer archives.
# If not specified at cmd line or config file, set to ./archives/peers
if (defined($peer_out_dir)) {
    $config{peer_out_dir} = $peer_out_dir;
} elsif (!defined($config{peer_out_dir})) {
    $config{peer_out_dir} = "$cwd/archives/peers";
}

# Set the path for the archiver to store status messages.
if (defined($status_file)) {
    $config{status_file} = $status_file;
} elsif (!defined($config{status_file})) {
    $config{status_file} = "$cwd/archiver_status";
}

# Check if we write the pid
if (defined($no_pid)) {
    $config{no_pid} = 1;
}

# Check if we archive RIBs.
if (defined($ribs) && $ribs == 1) {
    $config{ribs} = 1;
    $config{port} = DEFAULT_RIB_PORT;
} else {
    $config{ribs} = 0;
}

#---- Initialize the log. ----
if (BGPmon::Log::log_init(use_syslog => $config{use_syslog},
        log_level => $config{log_level},
        log_file => $config{log_file},
        prog_name => $prog_name) != 0) {
    my $err_msg = BGPmon::Log::get_error_message('log_init');
    print STDERR "Error initializing log: $err_msg\n";
    exit 1;
}

#---- Open the archiver status file. If there is an error opening the
# status file, archiver will log status messages to STDOUT. ----
unless (open($status_fh, ">>$config{status_file}")) {
    if (defined($is_daemon) && $is_daemon == 1) {
        BGPmon::Log::log_err("Could not open status file for writing. Exiting.");
        BGPmon::Log::log_close();
        exit 1;
    } else {
        BGPmon::Log::log_warn("Could not open status file for writing. Writing status messages to STDOUT.");
        $status_fh = *STDOUT;
        $use_stdout_for_status = 1;
    }
}

#---- Set time to an early date so first message will trigger file creation. ----
my $epoch = time();
my $start_time = $epoch - 2 * $config{roll_interval};
#---- Round down to even intervals for start and end times. ----
$start_time -= ($start_time % $config{roll_interval});
my $end_time = $start_time + 2 * $config{roll_interval};

#---- Daemonize if needed. ----
if (defined($is_daemon) && $is_daemon == 1) {
    daemonize();
} else {
    write_pid_file();
}

#---- Print status message to archiver status file. ----
write_status_message("STARTED:");

#---- Connect to the BGPmon instance. ----
BGPmon::Log::log_info("Connecting to BGPmon server at
    $config{server} port $config{port}");
unless (BGPmon::Fetch::connect_bgpdata(
        $config{server}, $config{port}) == 0) {
    my $err_msg = BGPmon::Fetch::get_error_message('connect_bgpdata');
    BGPmon::Log::log_fatal("Could not connect to BGPmon server at $config{server} port $config{port}: $err_msg");
}

#---- Print status message to archiver status file. ----
write_status_message("CONNECTED: server=$config{server} port=$config{port}");

#---- Start a read forever loop to receive data from BGPmon. ---
my $xml_message = "";
while (1) {
    my $err_msg = "";
    $xml_message = BGPmon::Fetch::read_xml_message();

    # Check if we got a XML message.
    # If not, log warning and try to re-establish connection.
    unless (defined($xml_message)) {
        $err_msg = BGPmon::Fetch::get_error_message('read_xml_message');
        BGPmon::Log::log_warn("Error reading XML message from BGPmon: $err_msg");
        write_status_message("STOPPED: Failed to read XML message");

        foreach my $file (keys %file_fhs) {
            write_event_message($file, "STOPPED", "LOSTCONNECTION");
            close($file_fhs{$file});
            delete($file_fhs{$file});
        }

        until (BGPmon::Fetch::connect_bgpdata($config{server}, $config{port}) == 0) {
            $err_msg = BGPmon::Fetch::get_error_message('connect_bgpdata');
            BGPmon::Log::log_info("Could not reconnect to BGPmon: $err_msg. Sleeping $retry_interval seconds.");
            sleep($retry_interval);
        }

        BGPmon::Log::log_info("Reconnected to BGPmon ($config{server}, $config{port})");

        # Print status message to archiver status file.
        write_status_message("CONNECTED: server=$config{server} port=$config{port}");
        next;
    }

    # Check if we have a valid XML message.
    unless (valid_xml_message(\$xml_message)) {
        BGPmon::Log::log_warn("Skipping invalid XML message");
        next;
    }

    $messages_read++;

    # Check if the message meets the filtering criteria.
    unless (archive_xml_message(\$xml_message)) {
        BGPmon::Log::log_info(
            "XML message $messages_read did not meet archive criteria and will not be archived");
        next;
    }

    # Message will be archived. Write XML message to current output file.
    BGPmon::Log::debug(
        "XML message $messages_read met archive criteria and will be archived") if $debug;

    # Write the message to the appropriate file.
    unless (write_xml_message(\$xml_message, $config{roll_interval}) == 0) {
        BGPmon::Log::log_warn("Error writing xml message to output file.");
    }
}

#---- END main ----

#---- SIGINT Signal Handler ----
sub archiver_exit {
    # Clean up XML files before quitting.
    unless (cleanup_files() == 0) {
        BGPmon::Log::log_warn("Could not cleanup XML files before quitting.");
    }

    # Close connection to BGPmon
    close_connection();

    # Close the log.
    BGPmon::Log::log_close();

    # Print archiver status message that we are now stopped.
    write_status_message("STOPPED:");

    # Close the archiver status file.
    if ($use_stdout_for_status != 1) {
        close($status_fh);
    }

    # Delete PID file.
    my $pid_file = "/var/run/bgpmon-archiver/archiver.pid";
    if (-e $pid_file) {
        unlink($pid_file);
        if ($!) {
            print "Error deleting PID file $pid_file: $!\n";
        }
    }

    exit 0;
}

#---- Write PID file. ----
sub write_pid_file {
    if ($config{no_pid}) {
        return;
    }

    # Get PID.
    my $pid = getpid();

    # Set state directory.
    my $state_dir;
    if (defined($ENV{'ARCHIVER_STATE'})) {
        $state_dir = $ENV{'ARCHIVER_STATE'};
    } else {
        $state_dir = "/var/run/bgpmon-archiver";
    }

    # Open pid file and write pid. Close file after writing pid.
    my $pid_file = "$state_dir/archiver.pid";
    my $pid_file_fh;
    if (open ($pid_file_fh, ">$pid_file")) {
        my $bytes_written = syswrite($pid_file_fh, "$pid\n");
        if (!defined($bytes_written) || $bytes_written == 0) {
            print $pid;
        }
        close($pid_file_fh);
    } else {
        print "Could not open PID file $pid_file. Archiver PID is $pid.\n";
    }
}

#---- Put the archiver in daemon mode. ----
sub daemonize {
    # Fork and exit parent. Makes sure we are not a process group leader.
    my $pid = fork;
    exit 0 if $pid;
    exit 1 if not defined $pid;

    # Become leader of a new session, group leader of new
    # process group and detach from any terminal.
    setsid();
    $pid = fork;
    exit 0 if $pid;
    exit 1 if not defined $pid;

    # Change directory to / so that we don't block this filesystem.
    chdir '/' or die ("Could not chdir to /: $!");

    # Clear umask for file creation.
    umask 0;

    # Write pid file.
    write_pid_file();
}

#---- Write a status message to archiver status file. ----
sub write_status_message {
    my $msg = shift;
    my $header = strftime("%Y-%m-%d %H:%M:%S GMT", gmtime());
    my $status_msg = "$header $msg\n";
    my $bytes_written = syswrite($status_fh, $status_msg);
    if (!defined($bytes_written) || $bytes_written == 0) {
        BGPmon::Log::log_err("Could not write status message to status file: $status_msg");
    }
}

#---- Write an archiver status message to an open file ----
sub write_event_message {
    my ($file_name, $event, $cause) = @_;
    my $now = time();
    my $msg = "This will be replaced be an event message.";
    if ($file_name =~ /xml/) {
        my $date_time = strftime("%Y-%m-%dT%H:%M:%SZ", gmtime($now));
        $msg = "<ARCHIVER><TIME timestamp=\"$now\" datetime=\"$date_time\"/><EVENT cause=\"$cause\">$event</EVENT></ARCHIVER>\n";
    } else {
        $msg = "ARCHIVER|$now|$event|$cause\n";
    }

    my $bytes_written = syswrite($file_fhs{$file_name}, $msg);
    if (!defined($bytes_written) || $bytes_written == 0) {
        BGPmon::Log::log_err("Could not write status message to file $file_name: $msg");
    }
}

#---- Read the config file. ----
sub parse_config_file {
    my $conf_file = shift;

    my $conf_fh;
    unless (open($conf_fh, $conf_file)) {
        return -1;
    }

    # Start reading the file.
    my $line;
    my $param;
    my $value;
    my @line_elems;

    while ($line = <$conf_fh>) {
        chomp($line);

        # Sanity check .. Remove any trailing white space.
        $line =~ s/^\s+//g;

        # If the line starts with a #, skip it.
        next if ($line =~ /^\s*#/);

        # If the line is blank, skip it.
        next if ($line =~ /^$/);

        # Split line to get parameter and value.
        @line_elems = split(/\=/, $line);
        $param = $line_elems[0];
        $value = $line_elems[1];

        # Remove any spaces before and after the = sign.
        $param =~ s/\s+$//g;
        $value =~ s/^\s+//g;

        # Check the parameter and set the appropriate variable.
        if ($param eq "server") { # BGPmon server name/ip address
            $config{server} = $value;
        } elsif ($param eq "port") { # Port to connect to BGPmon
            $config{port} = $value;
        } elsif ($param eq "archive") { # Archive ribs?
            if ($value eq "ribs") {
                $config{ribs} = 1;
            } else {
                $config{ribs} = 0;
            }
        } elsif ($param eq "directory") { # Output directory
            $config{out_dir} = $value;
        } elsif ($param eq "loglevel") { # Logging level
            unless ($value >= 0 && $value <= 7) {
                BGPmon::Log::log_warn("Logging level can be between 0 and 7, found $value.");
                next;
            }
            $config{log_level} = $value;
        } elsif ($param eq "syslog") { # Use syslog?
            if ($value != 1 && $value != 0) {
                BGPmon::Log::log_warn("In config file, parameter $param can have values 0 or 1, found $value. Not logging to syslog.");
                $config{use_syslog} = 0;
            } else {
                $config{use_syslog} = $value;
            }
        } elsif ($param eq "logfile") { # Path to log file.
            $config{log_file} = $value;
        } elsif ($param eq "bgpdump") { # Archive bgpdump format messages?
            if ($value != 1 && $value != 0) {
                BGPmon::Log::log_warn("In config file, parameter $param can have values 0 or 1, found $value. Not archiving bgpdump format messages.");
                $config{archive_bgpdump} = 0;
            } else {
                $config{archive_bgpdump} = $value;
            }
        } elsif ($param eq "statusfile") { # Location of archiver status file.
            $config{status_file} = $value;
        } elsif ($param eq "peerdirectory") { # Location of archives organized by peer.
            $config{peer_out_dir} = $value;
        }
    }
    close($conf_fh);
    return 0;
}

#---- Validate an XML message. ----
sub valid_xml_message {
    return 1;
}

#---- Decide if the XML message should be archived. ----
sub archive_xml_message {
    return 1;
}

#---- Write XML message to file. ----
sub write_xml_message {
    my ($xml_message, $roll_interval) = @_;
    BGPmon::Log::debug("Writing message $messages_read to file") if $debug;

    my $err_msg = "this is an error message";

    # Parse message and form hash.
    unless (BGPmon::Translator::XFB2PerlHash::Simple::init($$xml_message)) {
        $err_msg = BGPmon::Translator::XFB2PerlHash::Simple::get_error_code(
            'init');
        BGPmon::Log::log_warn($err_msg);
        return 1;
    }

    # Get message timestamp.
    my $xml_msg_time = BGPmon::Translator::XFB2PerlHash::Simple::get_timestamp();
    unless (defined($xml_msg_time)) {
        $err_msg = BGPmon::Translator::XFB2PerlHash::Simple::get_error_code(
            'get_timestamp');
        BGPmon::Log::log_warn($err_msg);
        return 1;
    }

    # Based on message time, check if we need to roll files.
    if (roll_files($roll_interval, $xml_msg_time) == 1) {
        BGPmon::Log::log_warn("Error rolling files.");
        return 1;
    }

    # Get message type. We archive UPDATE/TABLE messages and STATUS messages separately.
    my $xml_msg_type = BGPmon::Translator::XFB2PerlHash::Simple::get_xml_message_type();
    unless (defined($xml_msg_type)) {
        $err_msg = BGPmon::Translator::XFB2PerlHash::Simple::get_error_code(
            'get_xml_message_type');
        BGPmon::Log::log_warn($err_msg);
        return 1;
    }

    BGPmon::Log::debug("Message $messages_read has type $xml_msg_type.") if $debug;
    my $is_update_or_table = 0;
    my $peer_ip;
    if ($xml_msg_type eq "UPDATE" || $xml_msg_type eq "TABLE") {
        $is_update_or_table = 1;
        # Get peering tag.
        my $peering = BGPmon::Translator::XFB2PerlHash::Simple::get_peering();
        unless (%$peering) {
            $err_msg = BGPmon::Translator::XFB2PerlHash::Simple::get_error_code(
                'get_peering');
            BGPmon::Log::log_warn($err_msg);
            return 1;
        }
        # Get peer IP from peering tag
        $peer_ip = $peering->{'SRC_ADDR'}->{'ADDRESS'}->{'content'};
        unless (defined($peer_ip)) {
            BGPmon::Log::log_warn("Unable to get peer IP from XML message $messages_read");
            return 1;
        }
    } else {
        # Log everything else to a special peer.
        $peer_ip = "-1";
    }

    # Check which interval the xml start time falls into.
    my $interval;
    if ($xml_msg_time >= $start_time + $roll_interval) {
        $interval = $start_time + $roll_interval;
    } else {
        $interval = $start_time;
    }

    # Get the file handle for the file to write XML message to.
    my $xml_fh = get_file_handle($peer_ip, $interval, XML_SAFI);
    unless (defined($xml_fh)) {
        BGPmon::Log::log_warn("Unable to get correct file handle to write message.");
        return 1;
    }

    # Append new line to message and write to disk.
    $$xml_message .= "\n";
    my $bytes_written = syswrite($xml_fh, $$xml_message);
    if (!defined($bytes_written) || $bytes_written == 0) {
        BGPmon::Log::log_err("Error writing XML message to disk: $!");
        return -1;
    }

    # Increment counters.
    $messages_archived++;
    $curr_messages_archived++;

    BGPmon::Log::debug("Total messages read = $messages_read, total messages archived = $messages_archived") if $debug;

    # Archive bgpdump format messages if required.
    # Archive only UPDATE and TABLE messages.
    if ($config{archive_bgpdump} && $is_update_or_table == 1
        && $peer_ip ne "-1") {
        unless (write_bgpdump_messages($xml_message, $peer_ip, $interval) == 0) {
            return -1;
        }
    }

    return 0;
}

#---- Roll files if required ----
sub roll_files {
    my ($roll_interval, $xml_msg_time) = @_;

    # See if our message has a timestamp that is too early.
    if ($xml_msg_time < $start_time) {
        BGPmon::Log::log_warn("Archiver is expecting messages between $start_time and $end_time, but received a message with time $xml_msg_time.");
        $start_time = $xml_msg_time - 2 * $config{roll_interval};
        #---- Round down to even intervals for start and end times. ----
        $start_time -= ($start_time % $config{roll_interval});
        $end_time = $start_time + 2 * $config{roll_interval};
        BGPmon::Log::debug("Setting new start time to $start_time and end time to $end_time") if $debug;
        if (scalar(keys %file_fhs) != 0) {
            BGPmon::Log::log_warn("Processed messages but new message falls outside expected time range. Reseting time range to $start_time - $end_time");
            foreach my $file (keys %file_fhs) {
                write_event_message($file, "CLOSED", "RESET_START_TIME");
                close($file_fhs{$file});
                delete($file_fhs{$file});
            }
        } else {
            BGPmon::Log::log_info("Found no currently open files. Resetting time range to $start_time - $end_time.");
        }
        return 0;
    }

    # Check if the timestamp is in range.
    if ($xml_msg_time < $end_time) {
        return 0;
    }

    # We have a message in the next interval. Move forward.
    while ($xml_msg_time > $end_time) {
        BGPmon::Log::log_info("Time ($xml_msg_time) in message $messages_read exceeds file end time of $end_time. Rolling files and moving interval forward.");
        $start_time += $roll_interval;
        $end_time += $roll_interval;
        BGPmon::Log::debug("Setting start time to $start_time and end time to $end_time") if $debug;

        # Print status message to archiver status file.
        write_status_message("ROLLING: messages_archived:$curr_messages_archived");

        # Set counter for messages processed during current interval to 0.
        $curr_messages_archived = 0;
    }

    # Close and compress all currently open files less than start time.
    foreach my $file (keys %file_fhs) {
        close_file($file, $start_time);
    }

    return 0;
}

#---- Return XML file handle associated with the given peer. ----
sub get_file_handle {
    my ($peer_ip, $interval, $safi) = @_;

    my $file = gen_new_file($peer_ip, $interval, $safi);
    my @file_elems = split(/\//, $file);
    my $file_name = $file_elems[-1];

    # Check if there is a file handle open for this file name. Return if present.
    if (defined($file_fhs{$file})) {
        return $file_fhs{$file};
    }

    # No file handle .. generate one.
    my $fh;
    my $bytes_written = 0;
    if (!-e $file) {
        # File does not exist. Create new file.
        open($fh, ">>$file") or
            BGPmon::Log::log_fatal("Could not open new output file $file for writing: $!");
        # Add file handle to hash of file handles.
        $file_fhs{$file} = $fh;

        # XML file. Write opening <xml> tag to file.
        if ($safi == XML_SAFI) {
            # Write opening <xml> tag to new XML file.
            $bytes_written = syswrite($fh, "<xml>\n");
            if (!defined($bytes_written) || $bytes_written != 6) {
                BGPmon::Log::log_err("Error writing opening <xml> tag: $!");
                return undef;
            }
        }
        # Write event and status messages.
        write_event_message($file, "OPENED", "CREATE_NEW_FILE");
        write_status_message("OPENING: New file $file_name");
    } else {
        # The file already exists.
        open($fh, "+>>$file") or
            BGPmon::Log::log_fatal("Could not open existing output file $file: $!");
        # Add file handle to hash of file handles.
        $file_fhs{$file} = $fh;

        # Set file pointer 7 bytes from end of file.
        my $addr = sysseek($fh, -7, SEEK_END);
        # Check if the last 7 bytes are the string </xml>.
        # If they are, delete the last 7 bytes.
        my $line = <$fh>;
        chomp($line);
        if ($line eq "</xml>") {
            truncate($fh, $addr) or BGPmon::Log::log_error("Could not truncate file $file: $!");
        }

        # Write event and status messages.
        write_event_message($file, "OPENED", "RESUMING_OUTPUT_TO_FILE");
        write_status_message("OPENING: Existing file $file_name");
    }

    # Return newly created file handle.
    return $fh;
}

#---- Create and open new XML file. ----
sub gen_new_file {
    my ($peer_ip, $interval, $safi) = @_;

    # Set the base directory name to YYYY.MM.
    my $dir_name = strftime("%Y.%m/%d", gmtime($interval));
    BGPmon::Log::debug("New directory name is $dir_name.") if $debug;

    # If we are processing RIBS, make the RIBS directory, else make UPDATES.
    my $dir_path = join("/", $config{out_dir}, $dir_name);
    if ($config{ribs} == 1) {
        $dir_path = join("/", $dir_path, "RIBS");
    } else {
        $dir_path = join("/", $dir_path, "UPDATES");
    }

    make_dir($dir_path);

    # Set the current working directory to the newly created directory.
    $curr_dir_path = $dir_path;

    # Generate new XML file name.
    my $ts = strftime('%Y%m%d.%H%M', gmtime($interval));
    my $file_name = "";

    # Check if this is a status file or a update/rib file.
    if ($peer_ip eq "-1") {
        $file_name = join(".", "status", $ts);
    } else {
        if ($config{ribs} == 1) {
            $file_name = join(".", "ribs", $ts);
        } else {
            $file_name = join(".", "updates", $ts);
        }
        # Append peer ip tp file name.
        $file_name .= ".$peer_ip";
    }

    if ($safi == XML_SAFI) {
        $file_name .= ".xml";
    } else {
        my $fsafi = sprintf("%03d", $safi);
        $file_name .= ".bgpdump-$fsafi";
    }

    # Return the new file name.
    return "$curr_dir_path/$file_name";
}

#---- Given a directory path, create a new directory. ----
sub make_dir {
    my $dir_path = shift;

    # Create output directory if required.
    unless (-d $dir_path) {
        BGPmon::Log::debug("Creating new output directory $dir_path.") if $debug;
        make_path($dir_path, {error => \my $err, mode => 0755, });
        if (@$err) {
            for my $diag (@$err) {
                my ($file, $message) = %$diag;
                if ($file eq '') {
                    BGPmon::Log::log_fatal("General error creating output directory $dir_path: $message\n");
                } else {
                    BGPmon::Log::log_fatal("Error creating output directory $dir_path: $message\n");
                }
            }
            return -1;
        }
    }
    return 0;
}

#---- Write bgpdump messages to disk. ----
sub write_bgpdump_messages {
    my ($xml_message, $peer_ip, $interval) = @_;
    my $final_ret = 0;

    # Parse XML message to get array of bgpdump strings.
    my %bgpdump_strs = BGPmon::Translator::XFB2BGPdump::translate_message(
        $$xml_message);
    unless (%bgpdump_strs) {
        my $err_msg = BGPmon::Translator::XFB2BGPdump::get_error_message(
            'translate_message');
        BGPmon::Log::log_err($err_msg);
        return -1;
    }

    # Write BGPdump output lines to file. The SAFI values are the hash keys.
    my $bdump_fh;
    my $line;
    my $safi;
    my $bytes_written;

    foreach $safi (keys %bgpdump_strs) {
        # Get file handle to write to.
        $bdump_fh = get_file_handle($peer_ip, $interval, $safi);
        unless (defined($bdump_fh)) {
            BGPmon::Log::log_warn("Could not get file handle for <$safi, $peer_ip>.");
            $final_ret = -1;
            next;
        }

        # Write messages to file.
        foreach $line (@{$bgpdump_strs{$safi}}) {
            # Append a new line character to each line from the array.
            $line .= "\n";
            $bytes_written = syswrite($bdump_fh, $line);
            if (!defined($bytes_written) || $bytes_written == 0) {
                BGPmon::Log::log_err("Error writing bgpdump messages to disk: $!");
                $final_ret = -1;
            }
        }
    }
    return $final_ret;
}

#---- Cleanup and compress XML files. ----
sub cleanup_files {
    foreach my $file (keys %file_fhs) {
        close_file($file);
    }

    # Reset the file handle hash.
    undef %file_fhs;
    return 0;
}

#---- Close a given file name, after checking for the right interval. ----
sub close_file {
    my ($file, $time) = @_;
    my $final_ret = 0;

    #Get file name from full path.
    my @file_elems = split(/\//, $file);
    my $file_name = $file_elems[-1];
    if (defined($time)) {
        # If the file time is later than $time, do nothing.
        my @file_name_elems = split(/\./, $file_name);
        # Compare the year month times.
        my $f_yyyymm = $file_name_elems[1];
        my $yyyymm = strftime('%Y%m%d', gmtime($time));
        if ($yyyymm < $f_yyyymm) {
            # File year/month later than input year/month. Do nothing.
            return 0;
        }

        # Compare the hours and minutes.
        my $f_hhmm = $file_name_elems[2];
        my $hhmm = strftime('%H%M', gmtime($time));
        if ($hhmm < $f_hhmm) {
            # File hour/minutes later than input hour/minutes. Do nothing.
            return 0;
        }
    }

    # Write event message to file.
    write_event_message($file, "CLOSED", "ROLL_INTERVAL_REACHED");

    # Write trailing </xml> tag to XML files.
    if ($file =~ /xml/) {
        my $bytes_written = syswrite($file_fhs{$file}, "</xml>\n");
        if (!defined($bytes_written) || $bytes_written != 7) {
            BGPmon::Log::log_warn('Error writing closing "</xml>" tag to file.');
        }
    }

    # Close file associated with this file name. Delete hash entry.
    close($file_fhs{$file});
    delete($file_fhs{$file});

    # Print status message to archiver status file.
    write_status_message("CLOSING: file $file_name");

    # Get the peer information from the file name.
    my $peer_ip = "peer ip";
    my @file_name_elems = split(/\./, $file_elems[-1]);
    if (scalar(@file_name_elems) == 5) {
        # IPv6 peer address.
        $peer_ip = $file_name_elems[3];
    } elsif (scalar(@file_name_elems) == 8) {
        # IPv4 peer address.
        $peer_ip = join(".", @file_name_elems[3, 4, 5, 6]);
    } elsif (scalar(@file_name_elems) == 4) {
        # Status file has peer name of status.
        $peer_ip = "status";
    }

    # Make output directory.
    my $dir_name = strftime("%Y.%m", gmtime($start_time));
    BGPmon::Log::debug("New directory name is $dir_name.") if $debug;

    # If we are processing RIBS, make the RIBS directory, else make UPDATES.
    my $dir_path = join("/", $config{peer_out_dir}, $peer_ip, $dir_name);
    if ($config{ribs} == 1) {
        $dir_path = join("/", $dir_path, "RIBS");
    } else {
        $dir_path = join("/", $dir_path, "UPDATES");
    }

    # Make output directory if required.
    make_dir($dir_path);

    # Create symlink for current file in the appropriate path.
    my $link = $file_elems[-1];
    unless (-e "$dir_path/$link") {
        if (symlink($file, "$dir_path/$link") != 1) {
            BGPmon::Log::log_warn("Error creating symlink to file $file in $dir_path/$link: $!");
            $final_ret = 1;
        }
    }
    return $final_ret;
}
