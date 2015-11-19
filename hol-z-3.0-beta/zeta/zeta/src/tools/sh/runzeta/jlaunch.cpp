// jlaunch.cpp : Legt das Klassenverhalten für die Anwendung fest.
//

#include "stdafx.h"
#include "jlaunch.h"
#include <direct.h>

#ifdef _DEBUG
#define new DEBUG_NEW
#undef THIS_FILE
static char THIS_FILE[] = __FILE__;
#endif

/////////////////////////////////////////////////////////////////////////////
// CJlaunchApp

BEGIN_MESSAGE_MAP(CJlaunchApp, CWinApp)
	//{{AFX_MSG_MAP(CJlaunchApp)
		// HINWEIS - Hier werden Mapping-Makros vom Klassen-Assistenten eingefügt und entfernt.
		//    Innerhalb dieser generierten Quelltextabschnitte NICHTS VERÄNDERN!
	//}}AFX_MSG
	// ON_COMMAND(ID_HELP, CWinApp::OnHelp)
END_MESSAGE_MAP()

/////////////////////////////////////////////////////////////////////////////
// CJlaunchApp Konstruktion

CJlaunchApp::CJlaunchApp()
{
	// ZU ERLEDIGEN: Hier Code zur Konstruktion einfügen
	// Alle wichtigen Initialisierungen in InitInstance platzieren
}

/////////////////////////////////////////////////////////////////////////////
// Das einzige CJlaunchApp-Objekt

CJlaunchApp theApp;

/////////////////////////////////////////////////////////////////////////////
// CJlaunchApp Initialisierung

BOOL CJlaunchApp::InitInstance()
{
	// Standardinitialisierung
	// Wenn Sie diese Funktionen nicht nutzen und die Größe Ihrer fertigen 
	//  ausführbaren Datei reduzieren wollen, sollten Sie die nachfolgenden
	//  spezifischen Initialisierungsroutinen, die Sie nicht benötigen, entfernen.
#ifdef _AFXDLL
	Enable3dControls();			// Diese Funktion bei Verwendung von MFC in gemeinsam genutzten DLLs aufrufen
#else
	Enable3dControlsStatic();	// Diese Funktion bei statischen MFC-Anbindungen aufrufen
#endif
	char cmd[MAX_PATH];
	int n = strlen(m_pszHelpFilePath);
	while (n-- > 0 && m_pszHelpFilePath[n] != '\\');
	strncpy(cmd, m_pszHelpFilePath, n+1);
	cmd[n+1] = 0;
	strcat(cmd, "zeta.bat");	
	// m_sCmd = "c:\\zeta-1.5\\bin\\zeta.bat";

	BROWSEINFO info;
	char path[MAX_PATH];
	info.hwndOwner = NULL; // GetSafeHwnd();
	/*
	SHGetSpecialFolderLocation(
		NULL, CSIDL_PROFILE, &info.pidlRoot
	);
	*/
	info.pidlRoot = NULL;
	info.pszDisplayName = (LPTSTR)path;
	info.lpszTitle = "Select Folder To Start ZETA Within";
	info.ulFlags = 0; // BIF_NEWDIALOGSTYLE|BIF_USENEWUI|BIF_SHAREABLE
	info.lpfn = NULL;
	info.lParam = 0;
	info.iImage = 0;
	CoInitialize(NULL);
	LPITEMIDLIST res = SHBrowseForFolder(&info);
	if (res == NULL){
		exit(1);
		/*
		MessageBox(
			NULL, (LPCTSTR)"Error",
			
				(LPCTSTR)"Cannot Launch ZETA",
				0
		);
		*/
	}
	SHGetPathFromIDList(
		res,
		path
	);
	STARTUPINFO sinfo;
	PROCESS_INFORMATION pinfo;
	GetStartupInfo(&sinfo);
	int cres = CreateProcess(
				// NULL, (LPSTR)(LPCSTR)m_sCmd,
				cmd, NULL, // (LPSTR)(LPCSTR)m_sCmd, NULL,
				NULL,
				NULL,
				FALSE,
				CREATE_NO_WINDOW,
				NULL,
				path,
				&sinfo,
				&pinfo
			);		
	if (cres == 0){
		char msg[1024];
		FormatMessage(
			FORMAT_MESSAGE_FROM_SYSTEM,
			NULL,
			GetLastError(),
			0,
			msg,
			1024,
			NULL
		);
		MessageBox(
			NULL, (LPCTSTR)msg, 
			(LPCTSTR)"Cannot Launch ZETA",
			MB_OK | MB_ICONSTOP
		);
		exit(2);
	}		

	return FALSE;

}

