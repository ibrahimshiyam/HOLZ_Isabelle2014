// jlaunch.h : Haupt-Header-Datei f�r die Anwendung JLAUNCH
//

#if !defined(AFX_JLAUNCH_H__A7874693_59A0_11D4_B7F4_0050DA73432E__INCLUDED_)
#define AFX_JLAUNCH_H__A7874693_59A0_11D4_B7F4_0050DA73432E__INCLUDED_

#if _MSC_VER > 1000
#pragma once
#endif // _MSC_VER > 1000

#ifndef __AFXWIN_H__
	#error include 'stdafx.h' before including this file for PCH
#endif

#include "resource.h"		// Hauptsymbole

/////////////////////////////////////////////////////////////////////////////
// CJlaunchApp:
// Siehe jlaunch.cpp f�r die Implementierung dieser Klasse
//

class CJlaunchApp : public CWinApp
{
public:
	CJlaunchApp();

// �berladungen
	// Vom Klassenassistenten generierte �berladungen virtueller Funktionen
	//{{AFX_VIRTUAL(CJlaunchApp)
	public:
	virtual BOOL InitInstance();
	//}}AFX_VIRTUAL

// Implementierung
	TCHAR	m_DlgFile[_MAX_DIR];
	CString m_sCmd;
	//{{AFX_MSG(CJlaunchApp)
		// HINWEIS - An dieser Stelle werden Member-Funktionen vom Klassen-Assistenten eingef�gt und entfernt.
		//    Innerhalb dieser generierten Quelltextabschnitte NICHTS VER�NDERN!
	//}}AFX_MSG
	DECLARE_MESSAGE_MAP()
};


/////////////////////////////////////////////////////////////////////////////

//{{AFX_INSERT_LOCATION}}
// Microsoft Visual C++ f�gt unmittelbar vor der vorhergehenden Zeile zus�tzliche Deklarationen ein.
extern CJlaunchApp theApp;
#endif // !defined(AFX_JLAUNCH_H__A7874693_59A0_11D4_B7F4_0050DA73432E__INCLUDED_)
