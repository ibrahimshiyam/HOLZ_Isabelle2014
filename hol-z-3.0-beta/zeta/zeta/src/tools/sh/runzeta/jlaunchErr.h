#if !defined(AFX_JLAUNCHERR_H__29811011_5BDD_11D4_88D7_005056F10C41__INCLUDED_)
#define AFX_JLAUNCHERR_H__29811011_5BDD_11D4_88D7_005056F10C41__INCLUDED_

#if _MSC_VER > 1000
#pragma once
#endif // _MSC_VER > 1000
// jlaunchErr.h : Header-Datei
//

/////////////////////////////////////////////////////////////////////////////
// Dialogfeld jlaunchErr 

class jlaunchErr : public CDialog
{
// Konstruktion
public:
	jlaunchErr(CWnd* pParent = NULL);   // Standardkonstruktor

// Dialogfelddaten
	//{{AFX_DATA(jlaunchErr)
	enum { IDD = IDD_ERROR };
		// HINWEIS: Der Klassen-Assistent fügt hier Datenelemente ein
	//}}AFX_DATA


// Überschreibungen
	// Vom Klassen-Assistenten generierte virtuelle Funktionsüberschreibungen
	//{{AFX_VIRTUAL(jlaunchErr)
	public:
	virtual int DoModal();
	virtual BOOL Create(LPCTSTR lpszClassName, LPCTSTR lpszWindowName, DWORD dwStyle, const RECT& rect, CWnd* pParentWnd, UINT nID, CCreateContext* pContext = NULL);
	protected:
	virtual void DoDataExchange(CDataExchange* pDX);    // DDX/DDV-Unterstützung
	virtual void CalcWindowRect(LPRECT lpClientRect, UINT nAdjustType = adjustBorder);
	//}}AFX_VIRTUAL

// Implementierung
protected:

	// Generierte Nachrichtenzuordnungsfunktionen
	//{{AFX_MSG(jlaunchErr)
	virtual void OnOK();
	afx_msg void OnDoubleclickedOk();
	afx_msg void OnPaint();
	//}}AFX_MSG
	DECLARE_MESSAGE_MAP()
};

//{{AFX_INSERT_LOCATION}}
// Microsoft Visual C++ fügt unmittelbar vor der vorhergehenden Zeile zusätzliche Deklarationen ein.

#endif // AFX_JLAUNCHERR_H__29811011_5BDD_11D4_88D7_005056F10C41__INCLUDED_
