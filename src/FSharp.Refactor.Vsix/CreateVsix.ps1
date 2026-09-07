# Builds and packages the Visual Studio extension. A .vsix is an OPC zip:
# payload + extension.vsixmanifest + [Content_Types].xml — assembled by
# hand here because the VSSDK.BuildTools packaging targets predate
# SDK-style fsproj and fight it.
#
#     powershell -File CreateVsix.ps1
#     VSIXInstaller /rootSuffix:Exp artifacts\FSharp.Refactor.vsix   # test instance
#     VSIXInstaller artifacts\FSharp.Refactor.vsix                   # real VS
param([string]$Configuration = "Release", [switch]$NoFsac)

$ErrorActionPreference = "Stop"
$here = Split-Path -Parent $MyInvocation.MyCommand.Path
$repo = Resolve-Path (Join-Path $here "..\..")

dotnet build $here -c $Configuration
if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }

# the analyzers the sidecar loads: build both SDK flavors
dotnet build (Join-Path $repo "src\FSharp.Refactor.Analyzers") -c $Configuration
if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }

$staging = Join-Path $here "obj\vsix-staging"
if (Test-Path $staging) { Remove-Item -Recurse -Force $staging }
New-Item -ItemType Directory -Force $staging | Out-Null

$bin = Join-Path $here "bin\$Configuration\net48"

# only OUR payload — the editor/MEF assemblies come from Visual Studio
foreach ($dll in "FSharp.Refactor.Vsix.dll", "FSharp.Core.dll", "Newtonsoft.Json.dll") {
    Copy-Item (Join-Path $bin $dll) $staging
}

# the menu commands' registration. Hand-written rather than produced by
# CreatePkgDef.exe, which has to load the freshly built assembly to read
# its attributes and is denied that by Application Control here; see the
# file's own header. The compiled command table is not staged at all — it
# rides inside the assembly as the Menus.ctmenu managed resource, which is
# what UseManagedResourcesOnly on the package attribute means.
Copy-Item (Join-Path $here "FSharp.Refactor.Vsix.pkgdef") $staging

# analyzers for the FSAC sidecar (it skips the SDK flavor it cannot load)
$analyzerDir = Join-Path $staging "analyzers"
New-Item -ItemType Directory -Force $analyzerDir | Out-Null
Copy-Item (Join-Path $repo "src\FSharp.Refactor.Analyzers\bin\$Configuration\net8.0\FSharp.Refactor.Analyzers.dll") $analyzerDir
Copy-Item (Join-Path $repo "src\FSharp.Refactor.Analyzers.Ionide\bin\$Configuration\net8.0\FSharp.Refactor.Analyzers.Ionide.dll") $analyzerDir

Copy-Item (Join-Path $repo "LICENSE") $staging
Copy-Item (Join-Path $repo "icon.png") $staging

# FsAutoComplete itself, so the extension works on a machine without the
# global tool: the newest payload in the global tool store, or one
# installed into obj\fsac-tool for the purpose. FsacClient looks for
# fsac\fsautocomplete.dll beside the extension before the global tool.
if (-not $NoFsac) {
    function Find-FsacPayload([string]$storeRoot) {
        if (-not (Test-Path $storeRoot)) { return $null }
        $version = Get-ChildItem -Path $storeRoot -Directory |
            Sort-Object { [version]$_.Name } | Select-Object -Last 1
        if (-not $version) { return $null }
        $tools = Join-Path $version.FullName "fsautocomplete\$($version.Name)\tools"
        if (-not (Test-Path $tools)) { return $null }
        $tfm = Get-ChildItem -Path $tools -Directory |
            Sort-Object { [double]($_.Name -replace '^net', '') } | Select-Object -Last 1
        if (-not $tfm) { return $null }
        $any = Join-Path $tfm.FullName "any"
        if (Test-Path (Join-Path $any "fsautocomplete.dll")) { return $any } else { return $null }
    }

    $payload = Find-FsacPayload (Join-Path $env:USERPROFILE ".dotnet\tools\.store\fsautocomplete")
    if (-not $payload) {
        $toolDir = Join-Path $here "obj\fsac-tool"
        if (-not (Test-Path (Join-Path $toolDir ".store\fsautocomplete"))) {
            dotnet tool install fsautocomplete --tool-path $toolDir
            if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }
        }
        $payload = Find-FsacPayload (Join-Path $toolDir ".store\fsautocomplete")
    }
    if (-not $payload) { throw "fsautocomplete payload not found; pass -NoFsac to package without it" }

    Copy-Item -Recurse -LiteralPath $payload (Join-Path $staging "fsac")
    Write-Host "Bundled FsAutoComplete from $payload"
}

# the packaged manifest is the PROCESSED form: VS's own build strips the
# design-time d: namespace before packaging, and the installer's reader
# rejects manifests that still carry it
$manifest = [IO.File]::ReadAllText((Join-Path $here "source.extension.vsixmanifest"))
$manifest = $manifest -replace '\s+xmlns:d="[^"]*"', ''
$manifest = $manifest -replace '\s+d:\w+="[^"]*"', ''
$manifest = $manifest -replace '<\?xml[^>]*\?>\s*', ''

# ONE version source: the extension's user-visible version (Manage
# Extensions, the marketplace listing, upgrade detection) is stamped from
# Directory.Build.props, so a release bump cannot forget the vsix
$repoVersion = [regex]::Match(
    [IO.File]::ReadAllText((Join-Path $repo "Directory.Build.props")),
    '<Version>([^<]+)</Version>').Groups[1].Value
if (-not $repoVersion) {
    throw "No <Version> in Directory.Build.props; refusing to ship the manifest's 0.0.0 placeholder."
}
$manifest = $manifest -replace '(<Identity [^>]*Version=")[^"]+(")', "`${1}$repoVersion`${2}"
Write-Host "Stamped vsix version $repoVersion"

[IO.File]::WriteAllText((Join-Path $staging "extension.vsixmanifest"), $manifest)

# VSIX v3 servicing files: the modern installer engine refuses a package
# without manifest.json + catalog.json (shapes templated from a working
# marketplace vsix; sha256 may be null)
$vsixId = [regex]::Match($manifest, 'Identity Id="([^"]+)"').Groups[1].Value
$version = [regex]::Match($manifest, 'Identity Id="[^"]+" Version="([^"]+)"').Groups[1].Value
$displayName = [regex]::Match($manifest, '<DisplayName>([^<]+)</DisplayName>').Groups[1].Value

$payloadFiles = Get-ChildItem -LiteralPath $staging -Recurse -File
$totalSize = ($payloadFiles | Measure-Object Length -Sum).Sum

$fileEntries = ($payloadFiles | ForEach-Object {
        $rel = '/' + $_.FullName.Substring($staging.Length + 1).Replace('\', '/')
        '{"fileName":"' + $rel + '","sha256":null}'
    }) -join ','

$manifestJson = '{"id":"' + $vsixId + '","version":"' + $version + '","type":"Vsix","vsixId":"' + $vsixId +
'","extensionDir":"[installdir]\\Common7\\IDE\\Extensions\\fsrefact.vs","files":[' + $fileEntries +
'],"installSizes":{"targetDrive":' + $totalSize + '},"dependencies":{"Microsoft.VisualStudio.Component.CoreEditor":"17.0"}}'
[IO.File]::WriteAllText((Join-Path $staging "manifest.json"), $manifestJson)

$catalogJson = '{"manifestVersion":"1.1","info":{"id":"' + $vsixId + ',version=' + $version +
'","manifestType":"Extension"},"packages":[{"id":"Component.' + $vsixId + '","version":"' + $version +
'","type":"Component","extension":true,"dependencies":{"' + $vsixId + '":"' + $version +
'","Microsoft.VisualStudio.Component.CoreEditor":"17.0"},"localizedResources":[{"language":"en-US","title":"' +
$displayName + '","description":"' + $displayName + '"}]},{"id":"' + $vsixId + '","version":"' + $version +
'","type":"Vsix","payloads":[{"fileName":"FSharp.Refactor.vsix","size":' + $totalSize + '}],"vsixId":"' + $vsixId +
'","extensionDir":"[installdir]\\Common7\\IDE\\Extensions\\fsrefact.vs","installSizes":{"targetDrive":' + $totalSize + '}}]}'
[IO.File]::WriteAllText((Join-Path $staging "catalog.json"), $catalogJson)

# every extension in the payload needs a Default (the FSAC payload brings
# dozens), and OPC forbids empty-Extension Defaults, so each extensionless
# file gets an Override part entry instead
$known = @{ "vsixmanifest" = "text/xml"; "json" = "application/json" }
$extensions = $payloadFiles |
    ForEach-Object { $_.Extension.TrimStart('.').ToLowerInvariant() } |
    Where-Object { $_ } | Sort-Object -Unique
$defaults = ($extensions | ForEach-Object {
        $type = if ($known.ContainsKey($_)) { $known[$_] } else { "application/octet-stream" }
        "  <Default Extension=`"$_`" ContentType=`"$type`" />"
    }) -join "`n"
$overrides = ($payloadFiles | Where-Object { -not $_.Extension } | ForEach-Object {
        $rel = '/' + $_.FullName.Substring($staging.Length + 1).Replace('\', '/')
        "  <Override PartName=`"$rel`" ContentType=`"text/plain`" />"
    }) -join "`n"
$contentTypes = @"
<?xml version="1.0" encoding="utf-8"?>
<Types xmlns="http://schemas.openxmlformats.org/package/2006/content-types">
$defaults
$overrides
</Types>
"@
[IO.File]::WriteAllText((Join-Path $staging "[Content_Types].xml"), $contentTypes, (New-Object System.Text.UTF8Encoding $false))

$artifacts = Join-Path $here "artifacts"
New-Item -ItemType Directory -Force $artifacts | Out-Null
$vsix = Join-Path $artifacts "FSharp.Refactor.vsix"
if (Test-Path $vsix) { Remove-Item -Force $vsix }

# manual zip: .NET Framework's CreateFromDirectory writes backslash entry
# names, which the OPC reader silently drops — part names must use '/'
Add-Type -AssemblyName System.IO.Compression
Add-Type -AssemblyName System.IO.Compression.FileSystem
$archive = [System.IO.Compression.ZipFile]::Open($vsix, [System.IO.Compression.ZipArchiveMode]::Create)
try {
    Get-ChildItem -LiteralPath $staging -Recurse -File | ForEach-Object {
        $rel = $_.FullName.Substring($staging.Length + 1).Replace('\', '/')
        [System.IO.Compression.ZipFileExtensions]::CreateEntryFromFile($archive, $_.FullName, $rel) | Out-Null
    }
}
finally {
    $archive.Dispose()
}

Write-Host "Created $vsix"
