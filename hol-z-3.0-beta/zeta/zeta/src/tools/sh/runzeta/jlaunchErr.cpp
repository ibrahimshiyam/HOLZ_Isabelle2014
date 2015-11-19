// jlaunchErr.cpp: Implementierungsdatei
//

#include "stdafx.h"
#include "jlaunch.h"
#include "jlaunchErr.h"

#ifdef _DEBUG
#define new DEBUG_NEW
#undef THIS_FILE
static char THIS_FILE[] = __FILE__;
#endif

/////////////////////////////////////////////////////////////////////////////
// Dialogfeld jlaunchErr 


jlaunchErr::jlaunchErr(CWnd* pParent /*=NULL*/)
	: CDialog(jlaunchErr::IDD, pParent)
{
	//{{AFX_DATA_INIT(jlaunchErr)
		// HINWEIS: Der Klassen-Assistent fügt hier Elementinitialisierung ein
	//}}AFX_DATA_INIT
}


void jlaunchErr::DoDataExchange(CDataExchange* pDX)
{
	CDialog::DoDataExchange(pDX);
	//{{AFX_DATA_MAP(jlaunchErr)
		// HINWEIS: Der Klassen-Assistent fügt hier DDX- und DDV-Aufrufe ein
	//}}AFX_DATA_MAP
}


BEGIN_MESSAGE_MAP(jlaunchErr, CDialog)
	//{{AFX_MSG_MAP(jlaunchErr)
	ON_BN_DOUBLECLICKED(IDOK, OnDoubleclickedOk)
	ON_WM_PAINT()
	//}}AFX_MSG_MAP
END_MESSAGE_MAP()

/////////////////////////////////////////////////////////////////////////////
// Behandlungsroutinen für Nachrichten jlaunchErr 

int jlaunchErr::DoModal() 
{
	// TODO: Speziellen Code hier einfügen und/oder Basisklasse aufrufen
	
	return CDialog::DoModal();
}

BOOL jlaunchErr::Create(LPCTSTR lpszClassName, LPCTSTR lpszWindowName, DWORD dwStyle, const RECT& rect, CWnd* pParentWnd, UINT nID, CCreateContext* pContext) 
{
	// TODO: Speziellen Code hier einfügen und/oder Basisklasse aufrufen
	
	return CDialog::Create(IDD, pParentWnd);
}

void jlaunchErr::OnOK() 
{
	// TODO: Zusätzliche Prüfung hier einfügen
	
	CDialog::OnOK();
}

void jlaunchErr::OnDoubleclickedOk() 
{
	// TODO: Code für die Behandlungsroutine der Steuerelement-Benachrichtigung hier einfügen
	
}

void jlaunchErr::CalcWindowRect(LPRECT lpClientRect, UINT nAdjustType) 
{
	// TODO: Speziellen Code hier einfügen und/oder Basisklasse aufrufen
	
	CDialog::CalcWindowRect(lpClientRect, nAdjustType);
}

void jlaunchErr::OnPaint() 
{
	CPaintDC dc(this); // device context for painting
	
	// TODO: Code für die Behandlungsroutine für Nachrichten hier einfügen
	
	// Kein Aufruf von CDialog::OnPaint() für Zeichnungsnachrichten
}
