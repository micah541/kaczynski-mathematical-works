# Run `lake build` as a detached process (not a Claude Code background shell), so that it is not
# stopped by Claude Code's memory monitor. Output goes to .lake/build.log; the last line is
# "BUILD_EXIT <code>" when the build has finished.
param([string]$Threads = "2")
$root = Split-Path -Parent $PSScriptRoot
$log = Join-Path $root ".lake\build.log"
if (Test-Path $log) { Remove-Item $log }
$cmd = "set LEAN_NUM_THREADS=$Threads&& lake build > `"$log`" 2>&1 & echo BUILD_EXIT %ERRORLEVEL% >> `"$log`""
$p = Start-Process -FilePath cmd.exe -ArgumentList "/c", $cmd -WorkingDirectory $root -WindowStyle Hidden -PassThru
Write-Output "started build pid $($p.Id), log $log"
